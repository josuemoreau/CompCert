(** This file develops a finite, flat memory model that is used in the
  flat assembly languages. It is based on the memory model that is used
  in the dynamic semantics of all the others languages of the compiler.
  It defines a type [fmem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

From Coq Require Import Zwf.
Require Intv.
Require Archi.
Require Import Axioms Coqlib Maps Integers Floats AST Values.
Require Export Memdata Memtype.
Require Import Memory.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (ZMap.get (Ptrofs.unsigned b) (PMap.get 1%positive a)) (at level 1).

Definition unallocated_on (P: ptrofs -> Prop) (m: mem): Prop :=
  forall o, P o -> ~Mem.perm m 1%positive (Ptrofs.unsigned o) Max Nonempty.

(** * Abstract heap allocator *)

(** The following signature abstracts over the possible allocation strategies.
  It takes as an input and returns [state], which contains the data the
  allocator needs to store across multiple calls.
  The [unallocated] predicate specifies the part of the memory that the
  allocator considers as unallocated, and in which it will allocate.
  The address [a] returned by [alloc s m sz] must satisfy the following
  properties:
- [ [a]..[a+sz] ) can be indexed by the pointers of the architecture;
- the memory space pointed to by [a] is unallocated;
- the [unallocated] predicate on the new allocator state still covers
  unallocated space in [m];
- the pointer [a] is suitably aligned, as specified by the C99 standard.
*)

Module Type ALLOCATOR.

Parameter state: Type.
Parameter unallocated: state -> ptrofs -> Prop.
Parameter alloc: state -> mem -> ptrofs -> option (ptrofs * state).
Parameter empty: state.

Section ALLOC_AXIOMS.

Variables (s: state) (m: mem) (sz: ptrofs) (a: ptrofs) (s': state).

Axiom alloc_representable:
  alloc s m sz = Some (a, s') ->
  Ptrofs.unsigned a + Ptrofs.unsigned sz < Ptrofs.modulus.

Axiom alloc_fresh:
  alloc s m sz = Some (a, s') ->
  unallocated_on (unallocated s) m ->
  unallocated_on (fun o =>
    Ptrofs.unsigned a <= Ptrofs.unsigned o < Ptrofs.unsigned a + Ptrofs.unsigned sz) m.

Axiom alloc_unallocated:
  alloc s m sz = Some (a, s') ->
  forall o,
    unallocated s' o ->
    Ptrofs.unsigned o < Ptrofs.unsigned a
    \/ Ptrofs.unsigned a + Ptrofs.unsigned sz <= Ptrofs.unsigned o.

Axiom alloc_unallocated_on:
  alloc s m sz = Some (a, s') ->
  unallocated_on (unallocated s) m ->
  unallocated_on (unallocated s') m.

Axiom alloc_aligned:
  alloc s m sz = Some (a, s') ->
  (min_safe_alignment (Ptrofs.unsigned sz) | Ptrofs.unsigned a).

End ALLOC_AXIOMS.

End ALLOCATOR.

Module AllocatorFacts (A: ALLOCATOR).

Fact empty_unallocated:
  unallocated_on (A.unallocated A.empty) Mem.empty.
Proof. now intros o _; apply Mem.perm_empty. Qed.

End AllocatorFacts.

Module FMem (A: ALLOCATOR).

Definition not_ptr (v: val): bool :=
  match v with
  | Vptr _ _ => false
  | _ => true
  end.

Definition not_ptr_fragment (v: memval): Prop :=
  match v with
  | Fragment v _ _ => not_ptr v = true
  | _ => True
  end.

(** * Finite memory of size <= 2^|ptr|. *)

(** A finite memory is built upon CompCert's block memory model.
  It provides the following two additional properties:
- the memory has only one block;
- it does not store any [Vptr], as pointer values will now be [Vptrofs],
  and also because [Vptr] does not have any byte representation.
*)

Record fmem := mkfmem {
  fmem_mem:> Mem.mem';
  fmem_oneblock: Mem.nextblock fmem_mem = 2%positive;
  fmem_no_ptr:
    forall o, not_ptr_fragment (Mem.mem_contents fmem_mem)#o;
  fmem_allocator_state: A.state;
  fmem_unallocated: unallocated_on (A.unallocated fmem_allocator_state) fmem_mem
}.

Definition perm (m: fmem) (addr: ptrofs) (k: perm_kind) (p: permission): Prop :=
  Mem.perm m 1%positive (Ptrofs.unsigned addr) k p.

Definition perm_dec:
  forall m addr k p, {perm m addr k p} + {~ perm m addr k p}.
Proof. now intros; apply Mem.perm_dec. Defined.

Definition range_perm (m: fmem) (lo hi: ptrofs) (k: perm_kind) (p: permission): Prop :=
  Mem.range_perm m 1%positive (Ptrofs.unsigned lo) (Ptrofs.unsigned hi) k p.

Lemma range_perm_dec:
  forall m lo hi k p, {range_perm m lo hi k p} + {~ range_perm m lo hi k p}.
Proof. now intros; apply Mem.range_perm_dec. Defined.

Definition valid_access (m: fmem) (chunk: memory_chunk) (addr: ptrofs) (p: permission): Prop :=
  Mem.valid_access m chunk 1%positive (Ptrofs.unsigned addr) p.

Lemma valid_access_dec:
  forall m chunk ofs p,
  {valid_access m chunk ofs p} + {~ valid_access m chunk ofs p}.
Proof. now intros; apply Mem.valid_access_dec. Defined.

Definition valid_pointer (m: fmem) (addr: ptrofs): bool :=
  perm_dec m addr Cur Nonempty.

Definition match_ptrofs (v: val) : option ptrofs :=
  match v with
  | Vint n => if Archi.ptr64 then None else Some (Ptrofs.of_int n)
  | Vlong n => if Archi.ptr64 then Some (Ptrofs.of_int64 n) else None
  | _ => None
  end.

Definition load (chunk: memory_chunk) (m: fmem) (addr: ptrofs): option val :=
  Mem.load chunk m 1%positive (Ptrofs.unsigned addr).

Definition loadv (chunk: memory_chunk) (m: fmem) (addr: val): option val :=
  match match_ptrofs addr with
  | Some a =>
    if zle (Ptrofs.unsigned a + size_chunk chunk) Ptrofs.modulus
    then load chunk m a
    else None
  | _ => None
  end.

#[local] Obligation Tactic := idtac.

#[program]
Definition store (chunk: memory_chunk) (m: fmem) (addr: ptrofs) (v: val): option fmem :=
  match not_ptr v with
  | false => None
  | true =>
    match Mem.store chunk m 1%positive (Ptrofs.unsigned addr) v with
    | Some m' => Some (mkfmem m' _ _ (fmem_allocator_state m) _)
    | None => None
    end
  end.
Next Obligation.
  simpl; intros * Hv * H.
  rewrite Mem.nextblock_store with (1 := eq_sym H).
  now apply fmem_oneblock.
Qed.
Next Obligation.
  simpl; intros * Hv * H o.
  rewrite Mem.store_mem_contents with (1 := eq_sym H).
  rewrite PMap.gss.
  destruct (zlt (Ptrofs.unsigned o) (Ptrofs.unsigned addr)).
  { rewrite Mem.setN_outside. now apply fmem_no_ptr. lia. }
  destruct (zle (Ptrofs.unsigned addr + Z.of_nat (length (encode_val chunk v))) (Ptrofs.unsigned o)).
  { rewrite Mem.setN_outside. now apply fmem_no_ptr. lia. }
  rewrite <- (Zplus_minus (Ptrofs.unsigned addr) (Ptrofs.unsigned o)).
  rewrite Mem.setN_same by lia.
  assert (Hvl: Forall not_ptr_fragment (encode_val chunk v)).
  { destruct v; try discriminate; now destruct chunk; repeat constructor. }
  apply (proj1 (Forall_nth _ _) Hvl (Z.to_nat (Ptrofs.unsigned o - Ptrofs.unsigned addr))).
  lia.
Qed.
Next Obligation.
  simpl; intros * _ * H o U P.
  apply Mem.perm_store_2 with (1 := eq_sym H) in P.
  now apply (fmem_unallocated m) in P.
Qed.

Definition storev (chunk: memory_chunk) (m: fmem) (addr v: val): option fmem :=
  match match_ptrofs addr with
  | Some a =>
    if zle (Ptrofs.unsigned a + size_chunk chunk) Ptrofs.modulus
    then store chunk m a v
    else None
  | _ => None
  end.

End FMem.

