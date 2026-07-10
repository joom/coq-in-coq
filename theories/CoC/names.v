(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

From CoC Require Import list_utils.
From CoC Require Export ml_types.


  (** Type of partial name lists. *)
  Definition partial_names := list name.

  (** Decidable equality on names. *)
  Definition name_dec : forall x y : name, {x = y} + {x <> y}
   := name_eq_dec.

  (** Converts a natural number to a name. *)
  Definition var_of_nat (n : nat) : name := name_of_nat n.

  (** [var_of_nat] is injective. *)
  Lemma injective_var_of_nat :
   forall m n : nat, var_of_nat m = var_of_nat n -> m = n.
  Proof.
    unfold var_of_nat. intros. apply name_of_nat_inj. exact H.
  Qed.


  (** Order on name lists induced by insertion. *)
  Inductive ord_insert : list name -> list name -> Prop :=
      oi_intro :
        forall (x : name) (n : nat) (l1 l2 : list name),
        insert x n l1 l2 -> ord_insert l1 l2.


  (** Membership in firstn implies membership in original list. *)
  Lemma in_firstn_orig {A : Set} (k : nat) (x : A) (l : list A) :
    In x (firstn k l) -> In x l.
  Proof.
    revert l; induction k as [|k' IHk]; intros l Hin.
    - simpl in Hin; contradiction.
    - destruct l as [|h l'].
      + simpl in Hin; contradiction.
      + simpl in Hin. destruct Hin as [-> | Hin]; [left; auto | right; apply IHk; exact Hin].
  Qed.

  (** Membership in skipn implies membership in original list. *)
  Lemma in_skipn_orig {A : Set} (k : nat) (x : A) (l : list A) :
    In x (skipn k l) -> In x l.
  Proof.
    revert l; induction k as [|k' IHk]; intros l Hin.
    - exact Hin.
    - destruct l as [|h l'].
      + simpl in Hin; contradiction.
      + right; apply IHk; exact Hin.
  Qed.

  (** Auxiliary for well_founded_ord_insert: accessibility by length. *)
  Lemma well_founded_ord_insert_aux : forall (n : nat) (lst : list name), length lst = n -> Acc ord_insert lst.
  Proof.
    induction n as [|n' IH]; intros lst Hlen.
    - apply Acc_intro; intros lst0 Hord.
      inversion_clear Hord as [x k la lb Hins].
      apply insert_length in Hins.
      destruct lst; simpl in Hlen; [|discriminate]. simpl in Hins. lia.
    - apply Acc_intro; intros lst0 Hord.
      inversion_clear Hord as [x k la lb Hins].
      apply IH.
      apply insert_length in Hins. lia.
  Qed.

  (** [ord_insert] is well-founded. *)
  Lemma well_founded_ord_insert : well_founded ord_insert.
  Proof.
    red; intros lst. apply well_founded_ord_insert_aux with (n := length lst); auto.
  Qed.


  (** Removes a name from a list, returning the reduced list or a proof of absence. *)
  Definition remove :
   forall (x : name) (l : partial_names),
   {l1 : partial_names | exists n : nat, insert x n l1 l} + {~ In x l}.
  Proof.
(*
Realizer Fix remove {remove/2: name->(list name)->(sumor (list name)) :=
  [x,l]Cases l of
     nil => (inright ?)
   | (cons y l1) => Cases (name_dec x y) of
         left => (inleft ? l1)
       | right => Cases (remove x l1) of
                    (inleft v) => (inleft ? (cons ? y v))
                  | inright => (inright ?)
                  end
       end
   end}.
*)
    refine
     (fix remove (x : name) (l : partial_names) {struct l} :
        {l1 : partial_names | exists n : nat, insert x n l1 l} + {~ In x l} :=
        match
          l
          return
            ({l1 : partial_names | exists n : nat, insert x n l1 l} + {~ In x l})
        with
        | nil => inright _ _
        | y :: l1 =>
            match name_dec x y with
            | left found => inleft _ (exist _ l1 _)
            | right notfound =>
                match remove x l1 with
                | inleft (exist v rmvd) => inleft _ (exist _ (y :: v) _)
                | inright notin => inright _ _
                end
            end
        end).
    simpl; auto.

    rewrite found.
    exists 0; trivial with coc.

    inversion_clear rmvd.
    exists (S x0); auto with coc core arith datatypes.

    simpl; intros [-> | H].
    elim notfound; reflexivity.
    apply notin; exact H.
  Defined.


  (** Finds a fresh variable name not in the given list, starting from [n]. *)
  Definition find_free :
   forall (l : partial_names) (n : nat),
   {m : nat | n <= m &  ~ In (var_of_nat m) l}.
  Proof.
(*
Realizer <nat->nat>rec ffv :: :: { ord_insert }
  [l:partial_names][n:?]Cases (remove (var_of_nat n) l) of
      (inleft l1) => (ffv l1 (S n))
    | inright => n
    end.
*)
    intro l.
    apply Acc_rec with (R := ord_insert) (x := l).
    2: apply well_founded_ord_insert.
    clear l.
    intros l acc_hyp ffv n.
    refine
     match remove (var_of_nat n) l with
     | inleft (exist l1 rmvd as s) =>
         match ffv l1 _ (S n) with
         | exist2 m m_le m_notin => exist2 _ _ m _ _
         end
     | inright fresh => exist2 _ _ n _ _
     end; auto with arith.
    destruct rmvd as [k0 Hins].
    eapply oi_intro; eauto.

    red in |- *; intro Hin_l.
    apply m_notin.
    destruct rmvd as [k0 Hins].
    assert (Hneq : var_of_nat m <> var_of_nat n).
    { red in |- *; intro. enough (m = n) by lia. revert H; apply injective_var_of_nat. }
    clear m_le s ffv acc_hyp.
    destruct Hins as [Heq Hle]; subst l.
    apply in_app_or in Hin_l.
    destruct Hin_l as [Hin | [Heq | Hin]].
    - exact (in_firstn_orig k0 _ l1 Hin).
    - exfalso; apply Hneq; exact (eq_sym Heq).
    - exact (in_skipn_orig k0 _ l1 Hin).
  Defined.


  (** Finds a fresh variable name not occurring in the given list. *)
  Definition find_free_var : forall l : partial_names, {x : name | ~ In x l}.
  Proof.
(*
Realizer [l](var_of_nat (find_free l O)).
*)
    intros.
    elim (find_free l 0); intros; auto with coc.
    exists (var_of_nat x); trivial.
  Defined.


  (** Picks a display name from a hint list.  Returns the head hint when it is
      fresh for [l] (so user-supplied names survive), otherwise a guaranteed-fresh
      name from [find_free_var].  The second component is the unused tail of the
      hints, so callers can thread hints left-to-right down a binder spine.

      The returned name always carries a proof [~ In x l] — the exact contract of
      [find_free_var] — so no naming choice can capture: freshness is guaranteed
      by construction, independent of what the hints contain. *)
  Definition pick_name (hints : list name) (l : partial_names)
    : { x : name | ~ In x l } * list name.
  Proof.
    destruct hints as [| h rest].
    - exact (find_free_var l, nil).
    - destruct (in_dec name_dec h l).
      + exact (find_free_var l, rest).
      + exact (exist _ h n, rest).
  Defined.

  (** [pick_name] honours a fresh head hint: if [h] does not occur in [l], then
      the chosen name is exactly [h] and the leftover is the tail [rest]. *)
  Lemma pick_name_hint :
   forall (h : name) (rest : list name) (l : partial_names),
   ~ In h l ->
   proj1_sig (fst (pick_name (h :: rest) l)) = h /\ snd (pick_name (h :: rest) l) = rest.
  Proof.
    intros h rest l Hnotin. simpl.
    destruct (in_dec name_dec h l) as [Hin | Hni].
    - contradiction.
    - simpl. split; reflexivity.
  Qed.

  (** [pick_name] consumes at most the head of the hint list: the leftover is
      either the full hint list (when empty) or its tail. *)
  Lemma pick_name_leftover :
   forall (hints : list name) (l : partial_names),
   snd (pick_name hints l) = nil \/ snd (pick_name hints l) = tl hints.
  Proof.
    intros [| h rest] l; simpl.
    - left; reflexivity.
    - destruct (in_dec name_dec h l); simpl; right; reflexivity.
  Qed.


  (** Uniqueness predicate: each name occurs at most once in the list. *)
  Definition name_unique l :=
    forall (m n : nat) (x : name), nth_error l m = Some x -> nth_error l n = Some x -> m = n.


  (** Extending a unique name list with a fresh name preserves uniqueness. *)
  Lemma free_var_extension :
   forall l : partial_names,
   name_unique l -> forall x : name, ~ In x l -> name_unique (x :: l).
  Proof.
    unfold name_unique; intros l Huniq x Hnotin m n x0 Hm Hn.
    destruct m as [|m'], n as [|n']; simpl in *.
    - reflexivity.
    - injection Hm as Hm; subst x0.
      exfalso; apply Hnotin. apply (nth_error_In l n'). exact Hn.
    - injection Hn as Hn; subst x0.
      exfalso; apply Hnotin. apply (nth_error_In l m'). exact Hm.
    - f_equal. apply Huniq with x0; [exact Hm | exact Hn].
  Qed.


  (** In a unique list, item lookup yields a first-item witness. *)
  Lemma name_unique_first :
   forall (x : name) (l : partial_names) (n : nat),
   nth_error l n = Some x -> name_unique l -> first_item x l n.
  Proof.
    unfold first_item.
    intros x l n Hn Huniq.
    split; [exact Hn |].
    revert l n Hn Huniq.
    induction l as [|h l' IH]; intros n Hn Huniq.
    - destruct n; simpl in Hn; discriminate.
    - destruct n as [|n'].
      + simpl. intros []; tauto.
      + simpl in Hn. simpl. intros [Heq | Hin].
        * subst h.
          assert (H := Huniq 0 (S n') x).
          simpl in H. discriminate (H (eq_refl _) Hn).
        * assert (Huniq' : name_unique l').
          { unfold name_unique; intros m n0 y Hm Hn0.
            assert (H := Huniq (S m) (S n0) y).
            simpl in H. apply Nat.succ_inj. apply H; auto. }
          exact (IH n' Hn Huniq' Hin).
  Qed.
