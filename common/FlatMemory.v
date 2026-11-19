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

#[local]
Coercion Ptrofs.unsigned : ptrofs >-> Z.

Definition unallocated_on (P: ptrofs -> Prop) (m: mem): Prop :=
  forall o, P o -> ~Mem.perm m 1%positive o Max Nonempty.

(** * Abstract heap allocator *)

(** The following signature abstracts over the possible allocation strategies.
  It takes as an input and returns [state], which contains the data the
  allocator needs to store across multiple calls.
  The [unallocated] predicate specifies the part of the memory that the
  allocator considers as unallocated, and in which it will allocate.
  The address [a] returned by [reserve s m sz] must satisfy the following
  properties:
- [ [a]..[a+sz] ) can be indexed by the pointers of the architecture;
- only [ [a]..[a+sz] ) is reserved, the remaining memory is still
  unallocated;
- [ [a]..[a+sz] ) is disjoint from the memory that is still unallocated;
- the address [a] is suitably aligned, as specified by the C99 standard.
*)

Module Type ALLOCATOR.

Parameter state: Type.
Parameter unallocated: state -> ptrofs -> Prop.
Parameter reserve: state -> mem -> ptrofs -> option (ptrofs * state).
Parameter release: state -> ptrofs -> ptrofs -> option state.
Parameter empty: state.

Section RESERVE_AXIOMS.

Variables (s: state) (m: mem) (sz: ptrofs) (a: ptrofs) (s': state).

Axiom reserve_representable:
  reserve s m sz = Some (a, s') -> a + sz < Ptrofs.modulus.

Axiom reserve_unallocated:
  reserve s m sz = Some (a, s') ->
  forall (o: ptrofs),
    a <= o < a + sz \/ unallocated s' o -> unallocated s o.

Axiom reserve_unallocated_disj:
  reserve s m sz = Some (a, s') ->
  forall (o: ptrofs),
    unallocated s' o ->
    a <= o < a + sz ->
    False.

Axiom reserve_aligned:
  reserve s m sz = Some (a, s') ->
  (min_safe_alignment sz | a).

End RESERVE_AXIOMS.

Section RELEASE_AXIOMS.

Variables (s: state) (lo hi: ptrofs) (s': state).

Axiom release_unallocated_on:
  release s lo hi = Some s' ->
  forall (m: mem),
    unallocated_on (fun o => lo <= o < hi) m ->
    unallocated_on (unallocated s) m ->
    unallocated_on (unallocated s') m.

End RELEASE_AXIOMS.

End ALLOCATOR.

Module AllocatorFacts (A: ALLOCATOR).

Import A.

Fact empty_unallocated:
  unallocated_on (unallocated empty) Mem.empty.
Proof. now intros o _; apply Mem.perm_empty. Qed.

Section RESERVE_FACTS.

Variables (s: state) (m: mem) (sz: ptrofs) (a: ptrofs) (s': state).

Hypothesis (A: reserve s m sz = Some (a, s')).

Fact reserve_fresh:
  forall (o: ptrofs),
    a <= o < a + sz -> unallocated s o.
Proof.
  intros o Ho.
  apply reserve_unallocated with (1 := A).
  now left.
Qed.

Fact reserve_unallocated_1:
  forall (o: ptrofs),
    unallocated s' o -> unallocated s o.
Proof.
  intros o Ho.
  apply reserve_unallocated with (1 := A).
  now right.
Qed.

Fact reserve_unallocated_2:
  forall (o: ptrofs),
    unallocated s' o -> o < a \/ a + sz <= o.
Proof.
  intros o Ho.
  specialize (reserve_unallocated_disj _ _ _ _ _ A o Ho).
  lia.
Qed.

Fact reserve_fresh_unallocated_on:
  unallocated_on (unallocated s) m ->
  unallocated_on (fun o => a <= o < a + sz) m.
Proof.
  intros U o Ho; apply U.
  now apply reserve_fresh.
Qed.

Fact reserve_unallocated_on:
  unallocated_on (unallocated s) m ->
  unallocated_on (unallocated s') m.
Proof.
  intros U o Ho; apply U.
  now apply reserve_unallocated_1.
Qed.

End RESERVE_FACTS.

End AllocatorFacts.

Module FMem (A: ALLOCATOR).

Module AFacts := AllocatorFacts A.

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
  It requires the following two additional properties:
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
  fmem_unallocated: unallocated_on (A.unallocated fmem_allocator_state) fmem_mem;
}.

Definition perm (m: fmem) (addr: ptrofs) (k: perm_kind) (p: permission): Prop :=
  Mem.perm m 1%positive addr k p.

Definition perm_dec:
  forall m addr k p, {perm m addr k p} + {~ perm m addr k p}.
Proof. now intros; apply Mem.perm_dec. Defined.

Definition range_perm (m: fmem) (lo hi: ptrofs) (k: perm_kind) (p: permission): Prop :=
  Mem.range_perm m 1%positive lo hi k p.

Lemma range_perm_dec:
  forall m lo hi k p, {range_perm m lo hi k p} + {~ range_perm m lo hi k p}.
Proof. now intros; apply Mem.range_perm_dec. Defined.

Definition valid_access (m: fmem) (chunk: memory_chunk) (addr: ptrofs) (p: permission): Prop :=
  Mem.valid_access m chunk 1%positive addr p.

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
  Mem.load chunk m 1%positive addr.

Definition loadv (chunk: memory_chunk) (m: fmem) (addr: val): option val :=
  match match_ptrofs addr with
  | Some a =>
    if zle (a + size_chunk chunk) Ptrofs.modulus
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
    match Mem.store chunk m 1%positive addr v with
    | Some m' => Some (mkfmem m' _ _ (fmem_allocator_state m) _)
    | None => None
    end
  end.
Next Obligation.
  simpl; intros * Hv * H%eq_sym.
  rewrite Mem.nextblock_store with (1 := H).
  now apply fmem_oneblock.
Qed.
Next Obligation.
  simpl; intros * Hv * H%eq_sym o.
  rewrite Mem.store_mem_contents with (1 := H).
  rewrite PMap.gss.
  destruct (zlt o addr).
  { rewrite Mem.setN_outside. now apply fmem_no_ptr. lia. }
  destruct (zle (addr + Z.of_nat (length (encode_val chunk v))) o).
  { rewrite Mem.setN_outside. now apply fmem_no_ptr. lia. }
  rewrite <- (Zplus_minus addr o).
  rewrite Mem.setN_same by lia.
  assert (Hvl: Forall not_ptr_fragment (encode_val chunk v)).
  { destruct v; try discriminate; now destruct chunk; repeat constructor. }
  apply (proj1 (Forall_nth _ _) Hvl (Z.to_nat (o - addr))).
  lia.
Qed.
Next Obligation.
  simpl; intros * _ * H%eq_sym o U P.
  apply Mem.perm_store_2 with (1 := H) in P.
  now apply fmem_unallocated in P.
Qed.

Definition storev (chunk: memory_chunk) (m: fmem) (addr v: val): option fmem :=
  match match_ptrofs addr with
  | Some a =>
    if zle (a + size_chunk chunk) Ptrofs.modulus
    then store chunk m a v
    else None
  | _ => None
  end.

#[program]
Definition alloc_frame (m: fmem) (lo hi: Z): mem :=
  Mem.mkmem
    (Mem.mem_contents m)
    (PMap.set 1
      (fun ofs k =>
        if zle lo ofs && zlt ofs hi
        then Some Freeable
        else (Mem.mem_access m) !! 1 ofs k)
      (Mem.mem_access m))
    (Mem.nextblock m)
    _ _ _.
Next Obligation.
  intros; rewrite PMap.gsspec; case peq as [->|?].
  case (zle _ _ && zlt _ _). now simpl; apply perm_refl.
  now apply Mem.access_max. now apply Mem.access_max.
Qed.
Next Obligation.
  intros; rewrite PMap.gsspec; case peq as [->|?].
  case (zle _ _ && zlt _ _). now rewrite fmem_oneblock in H; elim H.
  now apply Mem.nextblock_noaccess. now apply Mem.nextblock_noaccess.
Qed.
Next Obligation.
  intros; now apply Mem.contents_default.
Qed.

Lemma alloc_frame_perm_1:
  forall m lo hi o,
    lo <= o < hi ->
    Mem.perm (alloc_frame m lo hi) 1%positive o Cur Freeable.
Proof.
  intros.
  unfold alloc_frame, Mem.perm; simpl; rewrite PMap.gss.
  destruct zle; [|lia]. destruct zlt; [|lia]. simpl.
  now apply perm_refl.
Qed.

Lemma alloc_frame_perm_2:
  forall (m: fmem) lo hi o k p,
    o < lo \/ hi <= o ->
    Mem.perm m 1%positive o k p ->
    Mem.perm (alloc_frame m lo hi) 1%positive o k p.
Proof.
  intros.
  unfold alloc_frame, Mem.perm; simpl; rewrite PMap.gss.
  destruct zle; [destruct zlt|]; simpl. lia. assumption. assumption.
Qed.

Lemma alloc_frame_perm_3:
  forall (m: fmem) lo hi o k p,
    o < lo \/ hi <= o ->
    Mem.perm (alloc_frame m lo hi) 1%positive o k p ->
    Mem.perm m 1%positive o k p.
Proof.
  intros * H.
  unfold alloc_frame, Mem.perm; simpl; rewrite PMap.gss.
  destruct zle; [destruct zlt|]; simpl. lia. easy. easy.
Qed.

#[program]
Definition alloc (m: fmem) (sz: ptrofs): option (fmem * ptrofs) :=
  match A.reserve (fmem_allocator_state m) m sz with
  | None => None
  | Some (a, s) =>
    Some (mkfmem
      (alloc_frame m a (a + sz))
      _ _ s _,
      a)
  end.
Next Obligation. now intros; apply fmem_oneblock. Qed.
Next Obligation. now intros; apply fmem_no_ptr. Qed.
Next Obligation.
  simpl; intros * A%eq_sym o U P.
  apply alloc_frame_perm_3 in P.
  2: now apply AFacts.reserve_unallocated_2 with (1 := A).
  apply AFacts.reserve_unallocated_on with (1 := A) (o := o).
  now apply fmem_unallocated. assumption. assumption.
Qed.

#[program]
Definition free (m: fmem) (lo hi: ptrofs): option fmem :=
  if range_perm_dec m lo hi Cur Freeable then
    match A.release (fmem_allocator_state m) lo hi with
    | None => None
    | Some s' =>
      Some (mkfmem
        (Mem.unchecked_free m 1%positive lo hi)
        _ _ s' _)
    end
  else None.
Next Obligation. now intros; simpl; apply fmem_oneblock. Qed.
Next Obligation. now intros; simpl; apply fmem_no_ptr. Qed.
Next Obligation.
  simpl; intros * P * F%eq_sym.
  apply (A.release_unallocated_on _ _ _ _ F).
- intros o Ho.
  unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gss; case zle; [|lia]; case zlt; [|lia]. easy.
- intros o Ho.
  specialize (fmem_unallocated m o Ho).
  unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gss. now case (_ && _).
Qed.

End FMem.

(** * Allocator model *)

(** To ensure the non-emptiness of the abstract allocator definition, we
  provide a trivial bump allocator implementation. *)

Module BumpAlloc <: ALLOCATOR.

Definition state := ptrofs.
Definition unallocated (s o: ptrofs) := s <= o.

Definition reserve (s: state) (m: mem) (sz: ptrofs): option (ptrofs * state) :=
  let lo := Z.lcm (min_safe_alignment sz) s in
  let hi := lo + sz in
  if zlt hi Ptrofs.modulus
  then Some (Ptrofs.repr lo, Ptrofs.repr hi)
  else None.

Definition release (s: state) (lo hi: ptrofs): option state := Some s.

Definition empty := Ptrofs.zero.

Section RESERVE_FACTS.

Variables (s: state) (m: mem) (sz: ptrofs) (a: ptrofs) (s': state).
Hypothesis A: reserve s m sz = Some (a, s').
Hypothesis U: unallocated_on (unallocated s) m.

Fact reserve_representable:
  a + sz < Ptrofs.modulus.
Proof.
  revert A; unfold reserve; destruct zlt; [intros [= <- <-]|discriminate].
  rewrite Ptrofs.unsigned_repr. assumption.
  split.
  - now apply Z.lcm_nonneg.
  - change Ptrofs.max_unsigned with (Ptrofs.modulus - 1).
    pose proof (Ptrofs.unsigned_range sz); lia.
Qed.

Fact lcm_le_r:
  forall x y, 0 < x -> 0 <= y -> y <= Z.lcm x y.
Proof.
  intros * Hx Hy.
  destruct (zeq y 0) as [->|].
  now rewrite Z.lcm_0_r.
  apply Z.divide_pos_le.
- pose proof (Z.lcm_nonneg x y).
  pose proof (Z.lcm_eq_0 x y).
  lia.
- now apply Z.divide_lcm_r.
Qed.

Let lo := Z.lcm (min_safe_alignment sz) s.
Let hi := lo + sz.

Fact lo_representable:
  hi < Ptrofs.modulus ->
  0 <= lo <= Ptrofs.max_unsigned.
Proof.
  pose proof (Ptrofs.unsigned_range sz).
  change Ptrofs.max_unsigned with (Ptrofs.modulus - 1).
  split. now apply Z.lcm_nonneg. lia.
Qed.

Fact hi_representable:
  hi < Ptrofs.modulus ->
  0 <= hi <= Ptrofs.max_unsigned.
Proof.
  intros H.
  generalize (lo_representable H).
  pose proof (Ptrofs.unsigned_range sz).
  change Ptrofs.max_unsigned with (Ptrofs.modulus - 1).
  lia.
Qed.

Fact reserve_unallocated:
  forall (o: ptrofs),
    a <= o < a + sz \/ unallocated s' o -> unallocated s o.
Proof.
  revert A; unfold reserve; destruct zlt; [intros [= <- <-]|discriminate].
  unfold unallocated.
  rewrite Ptrofs.unsigned_repr by now apply lo_representable.
  rewrite Ptrofs.unsigned_repr by now apply hi_representable.
  assert (s <= Z.lcm (min_safe_alignment sz) s) as Hlcm.
  { apply lcm_le_r.
    now apply Z.gt_lt, min_safe_alignment_pos.
    now apply Ptrofs.unsigned_range. }
  pose proof (Ptrofs.unsigned_range sz).
  lia.
Qed.

Fact reserve_unallocated_disj:
  forall (o: ptrofs),
    unallocated s' o ->
    a <= o < a + sz ->
    False.
Proof.
  revert A; unfold reserve; destruct zlt; [intros [= <- <-]|discriminate].
  unfold unallocated.
  rewrite Ptrofs.unsigned_repr by now apply hi_representable.
  rewrite Ptrofs.unsigned_repr by now apply lo_representable.
  lia.
Qed.

Fact reserve_aligned:
  (min_safe_alignment sz | a).
Proof.
  revert A; unfold reserve; destruct zlt; [intros [= <- <-]|discriminate].
  pose proof (Ptrofs.unsigned_range sz).
  rewrite Ptrofs.unsigned_repr by now apply lo_representable.
  now apply Z.divide_lcm_l.
Qed.

End RESERVE_FACTS.

Section RELEASE_FACTS.

Variables (s: state) (lo hi: ptrofs) (s': state).
Hypothesis F: release s lo hi = Some s'.

Fact release_unallocated_on:
  forall (m: mem),
    unallocated_on (fun o => lo <= o < hi) m ->
    unallocated_on (unallocated s) m ->
    unallocated_on (unallocated s') m.
Proof. now revert F; unfold release; intros [= <-]. Qed.

End RELEASE_FACTS.

End BumpAlloc.
