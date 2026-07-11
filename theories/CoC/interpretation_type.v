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


From CoC Require Import confluence.
From CoC Require Import typing.
From CoC Require Import classification.
From CoC Require Import candidates.
From CoC Require Import terms.

  (* Interpretation of type variables *)

  (** Interpretation of type variables as either a skeleton-indexed candidate or a type. *)
  Inductive interpretation_kind : Type :=
    | interp_knd : forall s : skeleton, candidate s -> interpretation_kind
    | interp_typ : interpretation_kind.

  (** Type interpretation environment. *)
  Definition interpretation_env := list interpretation_kind.


  (** Extract the class of an interpretation element. *)
  Definition class_of_interpretation_kind (ik : interpretation_kind) :=
    match ik with
    | interp_knd s _ => knd s
    | interp_typ => typ prop_skel
    end.


  (** Map an interpretation environment to a class environment. *)
  Definition classes_of_interpretation : interpretation_env -> class_list := map class_of_interpretation_kind.


  (** Extend an interpretation with a candidate guarded by the term's class. *)
  Definition extend_interpretation_kind (T : term) (ip : interpretation_env) (s : skeleton)
    (C : candidate s) :=
    match classify_term T (classes_of_interpretation ip) with
    | knd _ => interp_knd s C
    | _ => interp_typ
    end.


  (** Cons an extended interpretation element onto the environment. *)
  Definition interpretation_cons (T : term) (ip : interpretation_env) (s : skeleton)
    (C : candidate s) := cons (extend_interpretation_kind T ip s C) ip.


  (** Cons a default candidate onto the interpretation environment. *)
  Definition default_cons (T : term) (I : interpretation_env) : interpretation_env :=
    interpretation_cons T I _ (default_can (covariant_skeleton (classify_term T (classes_of_interpretation I)))).


  (** Skeleton of the class of a term under an interpretation. *)
  Definition skeleton_interpretation (t : term) (I : interpretation_env) :=
    type_skeleton (classify_term t (classes_of_interpretation I)).


  (** classes_of_interpretation (map class_of_interpretation_kind) commutes with firstn. *)
  Lemma classes_of_interpretation_firstn : forall (k : nat) (ip : interpretation_env),
    firstn k (classes_of_interpretation ip) = classes_of_interpretation (firstn k ip).
  Proof.
    unfold classes_of_interpretation; intros k ip; rewrite firstn_map; auto.
  Qed.

  (** classes_of_interpretation commutes with skipn. *)
  Lemma classes_of_interpretation_skipn : forall (k : nat) (ip : interpretation_env),
    skipn k (classes_of_interpretation ip) = classes_of_interpretation (skipn k ip).
  Proof.
    unfold classes_of_interpretation; intros k ip; rewrite skipn_map; auto.
  Qed.

  (** Inserting into an interpretation preserves the class environment. *)
  Lemma insert_in_classes :
   forall (c : class) (y : interpretation_kind) (k : nat) (ipe ipf : interpretation_env),
   class_of_interpretation_kind y = c ->
   insert y k ipe ipf -> insert c k (classes_of_interpretation ipe) (classes_of_interpretation ipf).
  Proof.
    unfold insert, classes_of_interpretation.
    intros c y k ipe ipf Hc [Heq Hle]; subst ipf c.
    split.
    - rewrite map_app. simpl.
      rewrite firstn_map, skipn_map. reflexivity.
    - rewrite length_map. exact Hle.
  Qed.


  (** Coerce an interpretation element to a candidate at a given skeleton. *)
  Definition coerce_candidate (s : skeleton) (i : interpretation_kind) : candidate s :=
    match i with
    | interp_knd si Ci =>
        match skeleton_eq_dec si s with
        | left y =>
            match y in (_ = x) return (candidate x) with
            | refl_equal => Ci
            end
        | _ => default_can s
        end
    | _ => default_can s
    end.

  (** Coercing a candidate preserves the is_can property. *)
  Lemma is_can_coerce :
   forall s s' C, is_can s C -> is_can s' (coerce_candidate s' (interp_knd s C)).
  Proof.
    simpl in |- *; intros s s' C Hcan.
    elim (skeleton_eq_dec s s'); intros Heq; [ case Heq; trivial | auto with coc ].
  Qed.

  Hint Resolve is_can_coerce: coc.


  (** Extracting a candidate at its own skeleton yields the original. *)
  Lemma extract_eq :
   forall (P : forall s : skeleton, candidate s -> Prop) (s : skeleton) (c : candidate s),
   P s c -> P s (coerce_candidate s (interp_knd s c)).
  Proof.
    intros P s c Hp.
    unfold coerce_candidate in |- *.
    elim (skeleton_eq_dec s s).
    intro Heq.
    change
      ((fun s0 (e : s = s0) =>
        P s0 match e in (_ = x) return (candidate x) with
             | refl_equal => c
             end) s Heq) in |- *.
    case Heq; trivial.
    simple induction 1; auto with coc core arith datatypes.
  Qed.


  (** Candidate equality is preserved by coercion. *)
  Lemma eq_can_extract :
   forall (s si : skeleton) (X Y : candidate s),
   eq_can s X Y -> eq_can si (coerce_candidate si (interp_knd s X)) (coerce_candidate si (interp_knd s Y)).
  Proof.
    unfold coerce_candidate in |- *.
    intros s si X Y Heq_can.
    elim (skeleton_eq_dec s si); auto with coc core arith datatypes.
    intro Heq; case Heq; auto with coc core arith datatypes.
  Qed.

  Hint Resolve eq_can_extract: coc.


  (** Pointwise equality of interpretation elements. *)
  Inductive interpretation_kind_eq : interpretation_kind -> interpretation_kind -> Prop :=
    | interp_eq_knd :
        forall (s : skeleton) (X Y : candidate s),
        eq_can s X X ->
        eq_can s Y Y -> eq_can s X Y -> interpretation_kind_eq (interp_knd s X) (interp_knd s Y)
    | interp_eq_typ : interpretation_kind_eq interp_typ interp_typ.

  Hint Resolve interp_eq_knd interp_eq_typ: coc.

  (** Reflexivity of interpretation element equality. *)
  Lemma interpretation_kind_inversion :
   forall (s : skeleton) (C : candidate s), eq_can s C C -> interpretation_kind_eq (interp_knd s C) (interp_knd s C).
  Proof.
    auto with coc core arith datatypes.
  Qed.

  Hint Resolve interpretation_kind_inversion: coc.


  (** Pointwise equality of interpretation environments. *)
  Definition interpretation_eq_can : interpretation_env -> interpretation_env -> Prop := Forall2 interpretation_kind_eq.

  (** Invariant: an interpretation is self-equal. *)
  Definition interpretation_invariant (i : interpretation_env) := interpretation_eq_can i i.

  Hint Unfold interpretation_eq_can interpretation_invariant: coc.


  (** Truncating an interpretation_env also truncates the classes_of_interpretation view. *)
  Lemma skipn_interpretation_classes :
   forall (k : nat) (ipf ipg : interpretation_env),
   ipg = skipn k ipf ->
   classes_of_interpretation ipg = skipn k (classes_of_interpretation ipf).
  Proof.
    unfold classes_of_interpretation.
    intros k ipf ipg H. subst.
    revert ipf; induction k as [|k' IH]; intros ipf.
    - simpl; auto.
    - destruct ipf as [|h ipf'].
      + simpl; auto.
      + simpl. apply IH.
  Qed.

  (* skipn_interpretation_classes NOT added as hint -- adding it breaks interpretation_stability proof structure *)

  (** Forall2 R (l1 ++ l2) (l1 ++ l2) implies Forall2 R l1 l1 and Forall2 R l2 l2. *)
  Lemma Forall2_app_self_inv {A : Type} (R : A -> A -> Prop) (l1 l2 : list A) :
    Forall2 R (l1 ++ l2) (l1 ++ l2) -> Forall2 R l1 l1 /\ Forall2 R l2 l2.
  Proof.
    revert l2; induction l1 as [|h l1' IHl]; intros l2 H.
    - simpl in H; auto.
    - simpl in H. inversion H as [|? ? ? ? Rhh Htail]; subst.
      destruct (IHl l2 Htail) as [Ha Hb].
      split; [constructor; auto | exact Hb].
  Qed.

  (** Insertion preserves the interpretation invariant. *)
  Lemma insert_interpretation_invariant :
   forall (e f : interpretation_env) (k : nat) (y : interpretation_kind),
   insert y k e f -> interpretation_invariant f -> interpretation_invariant e.
  Proof.
    unfold interpretation_invariant, interpretation_eq_can, insert.
    intros e f k y [Heq Hle] Hf; subst f.
    (* Hf : Forall2 interpretation_kind_eq (firstn k e ++ y :: skipn k e) (firstn k e ++ y :: skipn k e) *)
    apply Forall2_app_self_inv in Hf; destruct Hf as [H1 H2].
    inversion H2 as [|? ? ? ? _ Hskip]; subst.
    rewrite <- firstn_skipn with (n := k) (l := e).
    exact (Forall2_app H1 Hskip).
  Qed.


  (** interpretation_invariant implies interpretation_eq_can reflexivity. *)
  Lemma interpretation_invariant_eq_can : forall i : interpretation_env, interpretation_invariant i -> interpretation_eq_can i i.
  Proof.
    auto with coc core arith datatypes.
  Qed.

  Hint Resolve interpretation_invariant_eq_can: coc.


  (** Equal interpretations yield equal class environments. *)
  Lemma interpretation_eq_can_classes :
   forall i i' : interpretation_env, interpretation_eq_can i i' -> classes_of_interpretation i = classes_of_interpretation i'.
  Proof.
    unfold classes_of_interpretation in |- *.
    simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
    match goal with
    | Hxy : interpretation_kind_eq _ _,
      IH : map class_of_interpretation_kind _ = map class_of_interpretation_kind _ |- _ =>
        inversion_clear Hxy; simpl in |- *; intros; elim IH
    end; auto with coc core arith datatypes.
  Qed.


  (** Interpret a term as a candidate at a given skeleton. *)
  Fixpoint interpret_type (T : term) : interpretation_env -> forall s : skeleton, candidate s :=
    fun (ip : interpretation_env) (s : skeleton) =>
    match T with
    | sort_term _ => default_can s
    | var n => coerce_candidate s (nth n ip (interp_knd prop_skel strongly_normalizing))
    | lam A t =>
        match classify_term A (classes_of_interpretation ip) with
        | knd _ =>
            match s as x return (candidate x) with
            | prod_skel s1 s2 =>
                fun C : candidate s1 => interpret_type t (cons (interp_knd s1 C) ip) s2
            | prop_skel => default_can prop_skel
            end
        | typ _ => interpret_type t (default_cons A ip) s
        | _ => default_can s
        end
    | app u v =>
        match classify_term v (classes_of_interpretation ip) with
        | trm => interpret_type u ip s
        | typ sv => interpret_type u ip (prod_skel sv s) (interpret_type v ip sv)
        | _ => default_can s
        end
    | prod A B =>
        match s as x return (candidate x) with
        | prop_skel =>
            let s := covariant_skeleton (classify_term A (classes_of_interpretation ip)) in
            Pi s (interpret_type A ip prop_skel)
              (fun C => interpret_type B (interpretation_cons A ip s C) prop_skel)
        | prod_skel s1 s2 => default_can (prod_skel s1 s2)
        end
    end.
