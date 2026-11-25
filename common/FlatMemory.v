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

From Coq Require Import ZifyClasses.
Require Intv.
Require Archi.
Require Import Axioms Coqlib Maps Integers Floats AST Values.
Require Export Memdata Memtype.
Require Import Memory.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Create HintDb fmem.

(** * Simple extension of [lia] for pointer offsets. *)

#[program, local]
Instance InjPtrofs : InjTyp ptrofs Z := {|
  inj  := Ptrofs.unsigned;
  pred := (fun x => 0 <= x < Ptrofs.modulus);
|}.
Next Obligation. intros; simpl. apply Ptrofs.unsigned_range. Qed.
Add Zify InjTyp InjPtrofs.

#[program, local]
Instance InjPtrofs_unsigned : UnOp Ptrofs.unsigned :=
  {| TUOp x := x; TUOpInj := _ |}.
Add Zify UnOp InjPtrofs_unsigned.

#[program, local]
Instance InjPtrofs_max_unsigned : CstOp Ptrofs.max_unsigned :=
  {| TCst := Ptrofs.modulus - 1 |}.
Add Zify CstOp InjPtrofs_max_unsigned.

#[local]
Coercion Ptrofs.unsigned : ptrofs >-> Z.

(** * Some helper functions. *)

Definition unallocated_on (P: ptrofs -> Prop) (m: mem): Prop :=
  forall o, P o -> ~Mem.perm m 1%positive o Max Nonempty.

Lemma unallocated_on_implies (P Q: ptrofs -> Prop) m:
  unallocated_on P m ->
  (forall o, Q o -> P o) ->
  unallocated_on Q m.
Proof. intros U H o Ho. now apply U, H. Qed.

Lemma unallocated_on_perm (P: ptrofs -> Prop) m1 m2:
  unallocated_on P m1 ->
  (forall o k p,
    P o ->
    ~Mem.perm m1 1%positive o k p ->
    ~Mem.perm m2 1%positive o k p) ->
  unallocated_on P m2.
Proof. intros U H o Ho. apply H. easy. now apply U. Qed.

Hint Resolve unallocated_on_implies unallocated_on_perm : fmem.

Definition disjoint_regions (P1 P2: ptrofs -> Prop) : Prop :=
  forall o, P1 o -> P2 o -> False.

Lemma disjoint_regions_impl_l (P1 P2 Q: ptrofs -> Prop):
  disjoint_regions P1 Q ->
  (forall o, P2 o -> P1 o) ->
  disjoint_regions P2 Q.
Proof. intros D H o p q; apply D with (2 := q); apply H; assumption. Qed.

Lemma disjoint_regions_impl_r(P Q1 Q2: ptrofs -> Prop):
  disjoint_regions P Q1 ->
  (forall o, Q2 o -> Q1 o) ->
  disjoint_regions P Q2.
Proof. intros D H o p q; apply D with (1 := p); apply H; assumption. Qed.

Hint Resolve disjoint_regions_impl_l disjoint_regions_impl_r : fmem.

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

  The [release] function gives the unallocated range [ [lo]..[hi] ) to the
  allocator. It must satisfy the following two properties:
- any unallocated offset before [release] remains unallocated;
- the unallocated offsets after [release] either were unallocated before or
  are in the range [ [lo]..[hi] ).
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
  disjoint_regions (unallocated s') (fun o => a <= o < a + sz).

Axiom reserve_aligned:
  reserve s m sz = Some (a, s') ->
  (min_safe_alignment sz | a).

End RESERVE_AXIOMS.

Hint Resolve reserve_representable reserve_unallocated
  reserve_unallocated_disj reserve_aligned : fmem.

Section RELEASE_AXIOMS.

Variables (s: state) (lo hi: ptrofs) (s': state).

Axiom release_unallocated_1:
  release s lo hi = Some s' ->
  forall (o: ptrofs),
    unallocated s o -> unallocated s' o.

Axiom release_unallocated_2:
  release s lo hi = Some s' ->
  forall (o: ptrofs),
    unallocated s' o -> lo <= o < hi \/ unallocated s o.

End RELEASE_AXIOMS.

Hint Resolve release_unallocated_1 release_unallocated_2 : fmem.

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
  simpl; lia.
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

Hint Resolve reserve_fresh reserve_unallocated_1
  reserve_unallocated_2 reserve_fresh_unallocated_on
  reserve_unallocated_on | 2 : fmem.

Section RELEASE_FACTS.

Variables (s: state) (lo hi: ptrofs) (s': state).

Hypothesis (R: release s lo hi = Some s').

Fact release_unallocated_on:
  forall m,
    unallocated_on (fun o => lo <= o < hi) m ->
    unallocated_on (unallocated s) m ->
    unallocated_on (unallocated s') m.
Proof.
  intros m U1 U2 o Ho.
  destruct (release_unallocated_2 _ _ _ _ R o Ho).
  now apply U1. now apply U2.
Qed.

End RELEASE_FACTS.

Hint Resolve release_unallocated_on : fmem.

End AllocatorFacts.

Parameter stack_size: ptrofs.

Local Notation "a # b" := (ZMap.get (Ptrofs.unsigned b) (PMap.get 1%positive a)) (at level 1).

Module Make (A: ALLOCATOR).

Module AFacts := AllocatorFacts A.
Import A AFacts.

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
  and also because [Vptr] does not have any byte representation;
- the unallocated heap, as seen by the allocated, is actually unallocated;
- the stack is separated from the heap;
- the unused part of the stack is actually unallocated.
*)

Record mem' := mkfmem {
  fmem_mem:> Mem.mem';
  fmem_oneblock: Mem.nextblock fmem_mem = 2%positive;
  fmem_no_ptr:
    forall o, not_ptr_fragment (Mem.mem_contents fmem_mem)#o;
  (* Heap allocation *)
  fmem_heap_allocator_state: A.state;
  fmem_heap_unallocated: unallocated_on (A.unallocated fmem_heap_allocator_state) fmem_mem;
  (* Stack allocation *)
  fmem_stack_usage: ptrofs;
  (* The stack starts at [Ptrofs.max_unsigned] instead of [Ptrofs.modulus].
     We loose one byte, but it is necessary to make sure that a zero-sized
     stack corresponds to a valid pointer. *)
  fmem_stack_heap_disj:
    disjoint_regions (fun o => Ptrofs.max_unsigned - stack_size <= o)
                     (A.unallocated fmem_heap_allocator_state);
  fmem_stack_unallocated:
    unallocated_on (fun o =>
      Ptrofs.max_unsigned - stack_size <= o < Ptrofs.max_unsigned - fmem_stack_usage) fmem_mem;
}.

Definition mem := mem'.

#[local]
Hint Resolve fmem_oneblock fmem_no_ptr fmem_heap_unallocated
  fmem_stack_heap_disj fmem_stack_unallocated : fmem.

#[local]
Arguments Z.sub : simpl never.

Definition perm (m: mem) (addr: ptrofs) (k: perm_kind) (p: permission): Prop :=
  Mem.perm m 1%positive addr k p.

Definition perm_dec:
  forall m addr k p, {perm m addr k p} + {~ perm m addr k p}.
Proof. now intros; apply Mem.perm_dec. Defined.

Definition range_perm (m: mem) (lo hi: ptrofs) (k: perm_kind) (p: permission): Prop :=
  Mem.range_perm m 1%positive lo hi k p.

Lemma range_perm_dec:
  forall m lo hi k p, {range_perm m lo hi k p} + {~ range_perm m lo hi k p}.
Proof. now intros; apply Mem.range_perm_dec. Defined.

Definition valid_access (m: mem) (chunk: memory_chunk) (addr: ptrofs) (p: permission): Prop :=
  Mem.valid_access m chunk 1%positive addr p.

Lemma valid_access_dec:
  forall m chunk ofs p,
  {valid_access m chunk ofs p} + {~ valid_access m chunk ofs p}.
Proof. now intros; apply Mem.valid_access_dec. Defined.

Definition match_ptrofs (v: val) : option ptrofs :=
  match v with
  | Vint n => if Archi.ptr64 then None else Some (Ptrofs.of_int n)
  | Vlong n => if Archi.ptr64 then Some (Ptrofs.of_int64 n) else None
  | _ => None
  end.

Definition load (chunk: memory_chunk) (m: mem) (addr: ptrofs): option val :=
  Mem.load chunk m 1%positive addr.

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val): option val :=
  match match_ptrofs addr with
  | Some a =>
    if zle (a + size_chunk chunk) Ptrofs.modulus
    then load chunk m a
    else None
  | _ => None
  end.

#[local] Obligation Tactic := idtac.

#[program]
Definition store (chunk: memory_chunk) (m: mem) (addr: ptrofs) (v: val): option mem :=
  match not_ptr v with
  | false => None
  | true =>
    match Mem.store chunk m 1%positive addr v with
    | Some m' => Some (mkfmem m' _ _ (fmem_heap_allocator_state m) _ (fmem_stack_usage m) _ _)
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
Next Obligation. intros; eauto with mem fmem. Qed.
Next Obligation. intros; eauto with mem fmem. Qed.
Next Obligation. intros; eauto with mem fmem. Qed.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val): option mem :=
  match match_ptrofs addr with
  | Some a =>
    if zle (a + size_chunk chunk) Ptrofs.modulus
    then store chunk m a v
    else None
  | _ => None
  end.

#[program]
Definition alloc_frame (m: mem) (lo hi: Z): Mem.mem :=
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

Lemma alloc_frame_unallocated_disj:
  forall m lo hi o,
    ~Mem.perm (alloc_frame m lo hi) 1%positive o Max Nonempty ->
    o < lo \/ hi <= o.
Proof.
  intros * H.
  destruct (zle lo o); [|lia]. destruct (zlt o hi); [|lia].
  elim H; apply Mem.perm_cur_max, Mem.perm_implies with (p1 := Freeable).
  now apply (alloc_frame_perm_1 m lo hi o). constructor.
Qed.

Lemma alloc_frame_perm_2:
  forall (m: mem) lo hi o k p,
    o < lo \/ hi <= o ->
    Mem.perm m 1%positive o k p ->
    Mem.perm (alloc_frame m lo hi) 1%positive o k p.
Proof.
  intros.
  unfold alloc_frame, Mem.perm; simpl; rewrite PMap.gss.
  destruct zle; [destruct zlt|]; simpl. lia. assumption. assumption.
Qed.

Lemma alloc_frame_perm_3:
  forall (m: mem) lo hi o k p,
    o < lo \/ hi <= o ->
    Mem.perm (alloc_frame m lo hi) 1%positive o k p ->
    Mem.perm m 1%positive o k p.
Proof.
  intros * H.
  unfold alloc_frame, Mem.perm; simpl; rewrite PMap.gss.
  destruct zle; [destruct zlt|]; simpl. lia. easy. easy.
Qed.

Hint Resolve alloc_frame_perm_1 alloc_frame_perm_2 alloc_frame_perm_3 : fmem.

#[program]
Definition alloc (m: mem) (sz: ptrofs): option (mem * ptrofs) :=
  match A.reserve (fmem_heap_allocator_state m) m sz with
  | None => None
  | Some (a, s) =>
    Some (mkfmem
      (alloc_frame m a (a + sz))
      _ _ s _ (fmem_stack_usage m) _ _,
      a)
  end.
Next Obligation. now intros; apply fmem_oneblock. Qed.
Next Obligation. now intros; apply fmem_no_ptr. Qed.
Next Obligation. intros; eauto 10 with fmem. Qed.
Next Obligation. intros; eauto with fmem. Qed.
Next Obligation.
  simpl; intros * A%eq_sym o Ho P.
  apply alloc_frame_perm_3 in P.
- now apply (fmem_stack_unallocated m o).
- destruct (zle a o); [|lia]. destruct (zlt o (a + sz)); [|lia].
  elim (fmem_stack_heap_disj m o). lia.
  now apply reserve_fresh with (1 := A).
Qed.

#[program]
Definition free (m: mem) (lo hi: ptrofs): option mem :=
  if zle hi (Ptrofs.max_unsigned - stack_size) then
    if range_perm_dec m lo hi Cur Freeable then
      match A.release (fmem_heap_allocator_state m) lo hi with
      | None => None
      | Some s' =>
        Some (mkfmem
          (Mem.unchecked_free m 1%positive lo hi)
          _ _ s' _ (fmem_stack_usage m) _ _)
      end
    else None
  else None.
Next Obligation. now intros; simpl; apply fmem_oneblock. Qed.
Next Obligation. now intros; simpl; apply fmem_no_ptr. Qed.
Next Obligation.
  simpl; intros * Hhi P * R%eq_sym.
  apply AFacts.release_unallocated_on with (1 := R).
- intros o Ho.
  unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gss; case zle; [|lia]; case zlt; [|lia]. easy.
- intros o Ho.
  specialize (fmem_heap_unallocated m o Ho).
  unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gss. now case (_ && _).
Qed.
Next Obligation.
  simpl; intros * Hhi P * R%eq_sym o Ho U.
  destruct (A.release_unallocated_2 _ _ _ _ R o U).
- lia.
- now apply (fmem_stack_heap_disj m o).
Qed.
Next Obligation.
  simpl; intros * Hhi P * R%eq_sym o Ho.
  unfold Mem.perm, Mem.unchecked_free; simpl.
  rewrite PMap.gss; destruct zle; [destruct zlt|]; simpl.
- lia.
- now apply (fmem_stack_unallocated m).
- now apply (fmem_stack_unallocated m).
Qed.

#[program]
Definition alloc_stack (m: mem) (sz: ptrofs) : option mem :=
  if zlt (fmem_stack_usage m + sz) stack_size then
    let hi := Ptrofs.max_unsigned - fmem_stack_usage m in
    let lo := hi - sz in
    Some (mkfmem
      (alloc_frame m lo hi) _ _ (fmem_heap_allocator_state m) _
      (Ptrofs.add (fmem_stack_usage m) sz) _ _)
  else None.
Next Obligation. now intros; apply fmem_oneblock. Qed.
Next Obligation. now intros; apply fmem_no_ptr. Qed.
Next Obligation.
  intros * H hi lo o U P.
  apply (fmem_heap_unallocated m) with (1 := U).
  destruct (zle lo o).
- elim (fun H => fmem_stack_heap_disj m o H U); lia.
- now apply alloc_frame_perm_3 with (2 := P); left; apply Z.gt_lt.
Qed.
Next Obligation. now intros; apply fmem_stack_heap_disj. Qed.
Next Obligation.
  intros * H hi lo o.
  unfold Ptrofs.add; rewrite Ptrofs.unsigned_repr.
  intros Ho P. apply alloc_frame_perm_3 in P.
  apply (fmem_stack_unallocated m o). lia. eassumption. lia. lia.
Qed.

#[program]
Definition free_stack (m: mem) (sz: ptrofs) : option mem :=
  let lo := Ptrofs.max_unsigned - fmem_stack_usage m in
  let new_usage := Ptrofs.sub (fmem_stack_usage m) sz in
  let hi := Ptrofs.max_unsigned - new_usage in
  (* if zlt 0 sz then *)
  if zle sz (fmem_stack_usage m) then
    Some (mkfmem
      (Mem.unchecked_free m 1%positive lo hi)
      _ _ (fmem_heap_allocator_state m) _ new_usage _ _)
  else None.
  (* else Some m. *)
Next Obligation. now intros; apply fmem_oneblock. Qed.
Next Obligation. now intros; apply fmem_no_ptr. Qed.
Next Obligation.
  simpl; intros * Hsz o U P.
  apply (fmem_heap_unallocated m) with (1 := U).
  revert P; unfold Mem.perm, Ptrofs.sub; simpl; rewrite PMap.gss.
  rewrite Ptrofs.unsigned_repr by lia.
  destruct zle; [|easy]; destruct zlt; [|easy]. contradiction.
Qed.
Next Obligation. now intros; apply fmem_stack_heap_disj. Qed.
Next Obligation.
  simpl; intros * Hsz o.
  unfold Ptrofs.sub; rewrite Ptrofs.unsigned_repr by lia.
  intro Ho.
  unfold Mem.perm, Mem.unchecked_free; simpl; rewrite PMap.gss.
  destruct zle; [destruct zlt|]; simpl.
  easy. lia. apply (fmem_stack_unallocated m o); lia.
Qed.

End Make.

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
  split. now apply Z.lcm_nonneg. lia.
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
Proof. split. now apply Z.lcm_nonneg. lia. Qed.

Fact hi_representable:
  hi < Ptrofs.modulus ->
  0 <= hi <= Ptrofs.max_unsigned.
Proof. intros H. specialize (lo_representable H). lia. Qed.

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
  rewrite Ptrofs.unsigned_repr by now apply lo_representable.
  now apply Z.divide_lcm_l.
Qed.

End RESERVE_FACTS.

Section RELEASE_FACTS.

Variables (s: state) (lo hi: ptrofs) (s': state).
Hypothesis (R: release s lo hi = Some s').

Fact release_unallocated_1:
  forall (o: ptrofs),
    unallocated s o -> unallocated s' o.
Proof. now revert R; unfold release; intros [= <-]. Qed.

Fact release_unallocated_2:
  forall (o: ptrofs),
    unallocated s' o -> lo <= o < hi \/ unallocated s o.
Proof. now revert R; unfold release; intros [= <-]; right. Qed.

End RELEASE_FACTS.

End BumpAlloc.
