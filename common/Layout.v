Require Import Coqlib Integers Values Maps.

Import ListNotations.

(** * Stack layout *)

#[local]
Coercion Ptrofs.unsigned: ptrofs >-> Z.

(** The stack is located between [stack_lo] and [stack_hi].
  We define an additional [stack_region] predicate over addresses to cover
  the case where the stack region is larger than the writable part
  (e.g., to include the stack guard-page). *)

Record StackLayout := {
  stack_lo: ptrofs;
  stack_hi: ptrofs;
  stack_region: ptrofs -> Prop;
  stack_in_stack_region:
    forall (o: ptrofs), stack_lo <= o < stack_hi -> stack_region o
}.

(** * Global variables and functions layout *)

(** The global variables and functions can be placed anywhere.
  We define their placement by two [encode] and [decode] functions.
- [encode b o] returns an address, if possible, that corresponds
  to the place where the content associated to [(b, o)] will be stored
- [decode a] does the opposite, and returns a pair [(b, o)].

  They must satisfy the two following properties:
- applying [decode] on the result of [encode] gives the original pointer;
- [decode] maps the [sz]-bytes of [b] to a contiguous range of [sz] addresses.

  The record takes as parameter a [PTree.t positive] which represents
  the size of the blocks, which are the keys of the map.
  The sizes are [positive] to prevent two blocks from being placed
  at the same address in the memory. This could happen if one of them
  as size zero.
*)

Definition size_dom (objs: list (block * positive)) : N :=
  fold_right (fun '(b', sz) n => N.add (N.pos sz) n) 0%N objs.

Definition in_dom (b: block) (o: Z) (objs: PTree.t positive) :=
  exists sz, objs!b = Some sz /\ 0 <= o < Z.pos sz.

Record GlobalsLayout (objs: PTree.t positive) := {
  encode: block -> Z -> option ptrofs;
  decode: ptrofs -> option (block * Z);
  decode_encode:
    forall (b: block) (o: Z),
      Z.of_N (size_dom (PTree.elements objs)) < Ptrofs.modulus ->
      in_dom b o objs ->
      exists a, encode b o = Some a /\ decode a = Some (b, o);
  encode_contiguous:
    forall (b: block) (o: Z) (a1 a2: ptrofs),
      in_dom b o objs ->
      in_dom b (o + 1) objs ->
      encode b o = Some a1 ->
      encode b (o + 1) = Some a2 ->
      a2 = Ptrofs.add a1 Ptrofs.one;
}.

Section CONSISTENCY.

(** Consistency of the stack layout abstraction. *)

#[program]
Definition StackLayoutConsistent : StackLayout := {|
  stack_lo := Ptrofs.zero;
  stack_hi := Ptrofs.repr (2^20);
  stack_region := fun (o: ptrofs) => 0 <= o < 2^20
|}.

(** Consistency of the global variables and functions layout abstraction. *)

Definition base_address (objs: list (block * positive)) (b: block) : N :=
  fold_right (fun '(b', sz) n =>
    if plt b' b then N.add (N.pos sz) n else n) 0%N objs.

Definition search_block (objs: list (block * positive)) (a: N)
            : option (block * positive) :=
  find (fun '(b, sz) =>
    let base := base_address objs b in
    zle (Z.of_N base) (Z.of_N a) && zlt (Z.of_N a) (Z.of_N base + Z.pos sz)
  ) objs.

Lemma base_address_le_size_dom:
  forall objs b,
    (base_address objs b <= size_dom objs)%N.
Proof.
  intros *; unfold base_address, size_dom.
  induction objs; cbn -[N.add]; intros. now apply N.le_refl.
  destruct a; destruct plt; lia.
Qed.

Lemma base_address_le:
  forall objs b1 b2,
    (b1 < b2)%positive ->
    (base_address objs b1 <= base_address objs b2)%N.
Proof.
  intros * B; unfold base_address.
  induction objs; cbn -[N.add]; intros. now apply N.le_refl.
  destruct a; destruct plt; destruct plt; unfold Plt in *; lia.
Qed.

Lemma base_address_lt:
  forall objs b1 b2 sz1,
    In (b1, sz1) objs ->
    (b1 < b2)%positive ->
    (base_address objs b1 + N.pos sz1 <= base_address objs b2)%N.
Proof.
  intros * I B; unfold base_address.
  induction objs. contradiction.
  cbn -[N.add]. destruct I as [->|I].
- destruct plt as [H1|H1]; unfold Plt in H1; simpl in H1; [lia|].
  destruct plt as [H2|H2]; unfold Plt in H2; simpl in H2; [|lia].
  rewrite N.add_comm, <- N.add_le_mono_l.
  now apply base_address_le.
- apply IHobjs in I. destruct a; do 2 destruct plt; unfold Plt in *; lia.
Qed.

Lemma base_address_lt_size_dom:
  forall objs b sz,
    In (b, sz) objs ->
    (base_address objs b + N.pos sz <= size_dom objs)%N.
Proof.
  intros * I; unfold base_address, size_dom.
  induction objs. contradiction.
  cbn -[N.add]. destruct I as [->|I].
- destruct plt as [H1|H1]; unfold Plt in H1; simpl in H1; [lia|].
  rewrite N.add_comm, <- N.add_le_mono_l.
  now apply base_address_le_size_dom.
- apply IHobjs in I. destruct a; destruct plt; unfold Plt in *; lia.
Qed.

Lemma base_address_search_block:
  forall (objs: list (block * positive)) b sz (o: Z),
    Coqlib.list_norepet (map fst objs) ->
    In (b, sz) objs ->
    0 <= o < Z.pos sz ->
    search_block objs (base_address objs b + Z.to_N o) = Some (b, sz).
Proof.
  intros * R I Ho.
  remember (base_address objs b) as base eqn:Hbase.
  unfold search_block; set (F := fun _ => _).
  specialize (List.incl_refl objs).
  revert I R; induction objs at 1 2 3 5. contradiction.
  intros [->|I] R INCL.
- simpl; destruct zle; [destruct zlt|]; simpl. reflexivity.
  lia. lia.
- destruct a as [b' sz']; simpl in R.
  apply List.incl_cons_inv in INCL as [I' INCL].
  inversion_clear R.
  simpl; destruct zle; [destruct zlt|]; simpl; try now apply IHl.
  assert (b <> b').
  { intros <-. now apply (in_map fst) in I. }
  assert (b < b' \/ b' < b)%positive as B by lia.
  destruct B as [B|B].
  specialize (base_address_lt objs b b' sz (INCL _ I) B). lia.
  specialize (base_address_lt objs b' b sz' I' B). lia.
Qed.

Definition encode0 (objs: PTree.t positive) (b: block) o :=
  if zle 0 o then
    match objs!b with
    | None => None
    | Some sz =>
      if zlt o (Z.pos sz) then
        let base := base_address (PTree.elements objs) b in
        if zlt (Z.of_N base + o) Ptrofs.modulus then
          Some (Ptrofs.repr (Z.of_N base + o))
        else None
      else None
    end
  else None.

Definition decode0 (objs: PTree.t positive) (a: ptrofs) : option (block * Z) :=
  match search_block (PTree.elements objs) (Z.to_N a) with
  | None => None
  | Some (b, _) =>
    let base := base_address (PTree.elements objs) b in
    Some (b, a - Z.of_N base)
  end.

#[local] Obligation Tactic := idtac.

#[program]
Definition GlobalsLayoutConsistent (objs: PTree.t positive) : GlobalsLayout objs :=
  {| encode := encode0 objs; decode := decode0 objs |}.
Next Obligation.
  intros * H [sz [I Ho]].
  unfold encode0. destruct zle; [|lia]. rewrite I. destruct zlt; [|lia].
  apply PTree.elements_correct in I.
  pose proof (base_address_lt_size_dom (PTree.elements objs) b sz I).
  destruct zlt; [|lia].
  eexists; split. reflexivity.
  unfold decode0.
  change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in H.
  rewrite Ptrofs.unsigned_repr by lia.
  rewrite Z2N.inj_add, N2Z.id by lia.
  pose proof (PTree.elements_keys_norepet objs).
  rewrite (base_address_search_block (PTree.elements objs) b sz o) by assumption.
  now rewrite Z.add_simpl_l.
Qed.
Next Obligation.
  intros * [sz [I Ho]] [? [I' Ho']]; revert I'; rewrite I; intros [= <-].
  unfold encode0; rewrite I.
  do 2 (destruct zle; [|discriminate]). do 4 (destruct zlt; [|discriminate]).
  intros [= <-] [= <-].
  change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
  unfold Ptrofs.add; rewrite Ptrofs.unsigned_repr by lia.
  rewrite Z.add_assoc. reflexivity.
Qed.

End CONSISTENCY.
