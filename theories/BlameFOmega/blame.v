(** * BlameFOmega.blame: The Blame Theorem.

    Proves that [safe_pos_neg p] is preserved by one-step and multi-step
    reduction, and derives the Blame Theorem (Theorem 14) and its corollary
    (Corollary 15): a term whose casts carry positive/negative subtyping
    evidence never reduces to [blame p]. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From BlameFOmega Require Import syntax.
From BlameFOmega Require Import infrastructure.
From BlameFOmega Require Import semantics.
From BlameFOmega Require Import subtyping.
From BlameFOmega Require Import safety.

(** ** Blame Preservation *)

(** One-step preservation of [safe_pos_neg]: if [s] is safe and steps to [s'], so is [s']. *)
Lemma blame_preservation:
  forall s s' p,
  lbl_id p >= 2 ->
  safe_pos_neg p s -> [s ~> s'] -> safe_pos_neg p s'.
Proof.
  intros s s' p Hid Hsafe Hstep.
  revert Hsafe. induction Hstep; intros Hsafe; inversion Hsafe; subst; clear Hsafe.
  (* Contradictions *)
  all: try solve [exfalso; match goal with
    | H: negate ?p = ?p |- _ => exact (negate_neq p H)
    | H: ?p = negate ?p |- _ => symmetry in H; exact (negate_neq p H)
    | H: lbl_id ?p <> lbl_id ?p |- _ => apply H; reflexivity
    end].
  all: try solve [exfalso;
    repeat match goal with H: context [lbl_id (negate _)] |- _ => rewrite negate_id in H end;
    match goal with H: ?x <> ?x |- _ => apply H; reflexivity end].
  (* Tamper: blame with id 0 or 1 *)
  all: try solve [constructor; apply label_id_neq; simpl; lia].
  all: try solve [apply spn_blame; apply label_id_neq; simpl; lia].
  (* Simple congruence *)
  all: try solve [constructor; assumption].
  all: try solve [constructor; constructor; assumption].
  all: try solve [constructor; [assumption | constructor; assumption]].
  all: try solve [constructor; [constructor; assumption | assumption]].
  all: try solve [assumption].
  (* Beta *)
  all: try solve [
    apply safe_pos_neg_subst; [|assumption];
    match goal with H: safe_pos_neg _ (abs _ _) |- _ => inversion H; clear H; assumption end].
  (* TBeta: tapp (tabs K b) A ~> nu K A b *)
  all: try solve [
    apply spn_nu;
    match goal with H: safe_pos_neg _ (tabs _ _) |- _ =>
      inversion H; subst; clear H; assumption
    end].
  (* Wrap pos *)
  all: try solve [
    match goal with Hp: pos_subtype (arrow _ _) (arrow _ _) |- _ =>
      inversion Hp; subst; clear Hp; try discriminate;
      apply spn_abs; apply spn_cast_pos; [first [apply psub_refl | assumption] |];
      apply spn_app; [apply safe_pos_neg_lift; assumption |];
      apply spn_cast_neg; [first [apply nsub_refl | assumption] | apply spn_var]
    end].
  (* Wrap neg *)
  all: try solve [
    match goal with Hn: neg_subtype (arrow _ _) (arrow _ _) |- _ =>
      inversion Hn; subst; clear Hn; try discriminate;
      apply spn_abs; apply spn_cast_neg; [first [apply nsub_refl | assumption] |];
      apply spn_app; [apply safe_pos_neg_lift; assumption |];
      rewrite negate_negate; apply spn_cast_pos; [first [apply psub_refl | assumption] | apply spn_var]
    end].
  (* Wrap other *)
  all: try solve [
    apply spn_abs; apply spn_cast_other; [assumption |];
    apply spn_app; [apply safe_pos_neg_lift; assumption |];
    apply spn_cast_other; [rewrite negate_id; assumption | apply spn_var]].
  (* Ground pos *)
  all: try solve [
    apply spn_gnd; apply spn_cast_pos; [| assumption];
    match goal with
    | Hc: compat ?A _, Hg: ground _, Hnd: ?A <> dyn, Hng: ?A <> _, Hna: forall K A', ?A <> all K A' |- _ =>
      destruct (compat_ground_not_dyn_not_all_arrow _ _ Hc Hg Hnd Hng Hna)
        as [? [? [? ?]]]; subst; apply pos_subtype_arrow_arrow_dyn
    end].
  (* Ground neg *)
  all: try solve [
    apply spn_gnd; apply spn_cast_neg; [| assumption];
    match goal with
    | Hns: neg_subtype ?A dyn, Hc: compat ?A _, Hg: ground _, Hnd: ?A <> dyn, Hng: ?A <> _, Hna: forall K A', ?A <> all K A' |- _ =>
      destruct (compat_ground_not_dyn_not_all_arrow _ _ Hc Hg Hnd Hng Hna)
        as [? [? [? ?]]]; subst; apply neg_subtype_arrow_dyn_inv; assumption
    end].
  (* Ground other *)
  all: try solve [apply spn_gnd; apply spn_cast_other; assumption].
  (* Ground id *)
  all: try solve [apply spn_gnd; assumption].
  (* Collapse pos *)
  all: try solve [
    match goal with
    | Hspn: safe_pos_neg _ (gnd _ _) |- safe_pos_neg _ (cast _ _ _ _) =>
      inversion Hspn; subst; clear Hspn;
      apply spn_cast_pos; [apply pos_subtype_dyn_universal; assumption | assumption]
    end].
  (* Collapse neg *)
  all: try solve [
    match goal with
    | Hspn: safe_pos_neg _ (gnd _ _), Hg: ground ?G, Hc: compat ?G ?A
        |- safe_pos_neg _ (cast _ ?G ?A (negate _)) =>
      inversion Hspn; subst; clear Hspn;
      apply spn_cast_neg; [apply neg_subtype_ground_compat; assumption | assumption]
    end].
  (* Collapse other *)
  all: try solve [
    match goal with
    | Hspn: safe_pos_neg _ (gnd _ _) |- safe_pos_neg _ (cast _ _ _ _) =>
      inversion Hspn; subst; clear Hspn; apply spn_cast_other; assumption
    end].
  (* Conflict pos: contradiction — pos_subtype dyn A implies compat G A *)
  all: try solve [
    exfalso; match goal with
    | Hnc: ~ compat ?G ?A, Hg: ground ?G, Hps: pos_subtype dyn ?A |- _ =>
      apply Hnc; apply pos_subtype_dyn_compat_ground; assumption
    end].
  (* Conflict neg: blame (negate p), safe because negate p <> p *)
  all: try solve [apply spn_blame; apply negate_neq].
  (* Conflict other: blame q where lbl_id q <> lbl_id p *)
  all: try solve [apply spn_blame; apply label_id_neq; assumption].
  (* is_true/is_false *)
  all: try solve [repeat constructor].
  (* Generalize *)
  all: try solve [
    apply spn_tabs;
    match goal with
    | H: pos_subtype _ (all _ _), Hna: forall K' C, _ <> all K' C |- _ =>
      apply spn_cast_pos; [eapply pos_subtype_all_r_inv; [exact H | exact Hna] | apply safe_pos_neg_term_tlift; assumption]
    | H: neg_subtype _ (all _ _), Hna: forall K' C, _ <> all K' C |- _ =>
      apply spn_cast_neg; [eapply neg_subtype_all_r_inv; [exact H | exact Hna] | apply safe_pos_neg_term_tlift; assumption]
    end].
  all: try solve [
    apply spn_tabs;
    apply spn_cast_other; [assumption | apply safe_pos_neg_term_tlift; assumption]].
  (* Instantiate *)
  all: try solve [
    match goal with
    | H: pos_subtype (all _ _) _, Hna: forall K' B', _ <> all K' B' |- _ =>
      apply spn_cast_pos; [eapply pos_subtype_all_l_inv; [exact H | exact Hna] | apply spn_tapp; assumption]
    | H: neg_subtype (all _ _) _, Hna: forall K' B', _ <> all K' B' |- _ =>
      apply spn_cast_neg; [eapply neg_subtype_all_l_inv; [exact H | exact Hna] | apply spn_tapp; assumption]
    end].
  all: try solve [
    apply spn_cast_other; [assumption | apply spn_tapp; assumption]].
  (* Blame propagation *)
  all: try solve [
    match goal with
    | H: safe_pos_neg _ _ |- safe_pos_neg _ (blame _) =>
      inversion H; subst; clear H; apply spn_blame; assumption
    end].
  (* Congruence: IH cases — wrap in abstract to prevent evar leakage *)
  all: try solve [constructor; auto].
  (* Cast congruence *)
  all: try solve [
    match goal with
    | H: safe_pos_neg _ (cast _ _ _ _) |- _ =>
      inversion H; subst; clear H; clear H;
      first [apply spn_cast_pos | apply spn_cast_neg | apply spn_cast_other]; auto
    end].
  (* Wrap pos — remaining *)
  all: try solve [
    apply spn_abs; apply spn_cast_pos;
    [ match goal with H: pos_subtype (arrow _ _) (arrow _ _) |- _ =>
        inversion H; subst; clear H; [apply psub_refl | assumption] end
    | apply spn_app; [apply safe_pos_neg_lift; assumption |];
      apply spn_cast_neg;
      [ match goal with H: pos_subtype (arrow _ _) (arrow _ _) |- _ =>
          inversion H; subst; clear H; [apply nsub_refl | assumption]
        end
      | apply spn_var]]].
  (* Wrap neg — remaining *)
  all: try solve [
    apply spn_abs; apply spn_cast_neg;
    [ match goal with H: neg_subtype (arrow _ _) (arrow _ _) |- _ =>
        inversion H; subst; clear H; [apply nsub_refl | assumption] end
    | apply spn_app; [apply safe_pos_neg_lift; assumption |];
      rewrite negate_negate; apply spn_cast_pos;
      [ match goal with H: neg_subtype (arrow _ _) (arrow _ _) |- _ =>
          inversion H; subst; clear H; [apply psub_refl | assumption]
        end
      | apply spn_var]]].
  (* Collapse neg — remaining *)
  all: try solve [
    match goal with
    | Hspn: safe_pos_neg _ (gnd _ _) |- safe_pos_neg _ (cast _ _ _ (negate _)) =>
      inversion Hspn; subst; clear Hspn;
      apply spn_cast_neg; [apply nsub_dyn_l | assumption]
    end].
  (* Conflict pos — remaining *)
  all: try solve [
    match goal with
    | H6: safe_pos_neg _ (gnd _ _) |- safe_pos_neg _ (blame _) =>
      inversion H6; subst; clear H6; constructor; simpl in *; lia
    end].
  (* Conflict neg — remaining *)
  all: try solve [
    match goal with
    | H6: safe_pos_neg _ (gnd _ _) |- safe_pos_neg _ (blame (negate _)) =>
      inversion H6; subst; clear H6;
      apply spn_blame; simpl in *; try rewrite negate_id; lia
    end].
  (* Generalize — remaining *)
  all: try solve [
    apply spn_tabs;
    match goal with
    | H: pos_subtype _ (all _ _), Hna: forall K' C, _ <> all K' C |- _ =>
      apply spn_cast_pos; [eapply pos_subtype_all_r_inv; [exact H | exact Hna] |];
      apply safe_pos_neg_term_tlift; assumption
    | H: neg_subtype _ (all _ _), Hna: forall K' C, _ <> all K' C |- _ =>
      apply spn_cast_neg; [eapply neg_subtype_all_r_inv; [exact H | exact Hna] |];
      apply safe_pos_neg_term_tlift; assumption
    end].
  (* Instantiate — remaining *)
  all: try solve [
    match goal with
    | H: pos_subtype (all _ _) _, Hna: forall K' B', _ <> all K' B' |- _ =>
      apply spn_cast_pos; [eapply pos_subtype_all_l_inv; [exact H | exact Hna] |];
      apply spn_tapp; assumption
    | H: neg_subtype (all _ _) _, Hna: forall K' B', _ <> all K' B' |- _ =>
      apply spn_cast_neg; [eapply neg_subtype_all_l_inv; [exact H | exact Hna] |];
      apply spn_tapp; assumption
    end].
  (* tabs_congr: safe_pos_neg p (tabs K e), e ~> e' => safe_pos_neg p (tabs K e') *)
  all: try solve [
    match goal with H: safe_pos_neg _ (tabs _ _) |- _ =>
      inversion H; subst; clear H; apply spn_tabs; auto
    end].
  (* tabs_blame: safe_pos_neg p (tabs K (blame q)) => safe_pos_neg p (blame q) *)
  all: try solve [
    match goal with H: safe_pos_neg _ (tabs _ _) |- _ =>
      inversion H; subst; clear H;
      match goal with H2: safe_pos_neg _ (blame _) |- _ =>
        inversion H2; subst; apply spn_blame; assumption
      end
    end].
  (* nu_var: safe_pos_neg p (nu K A (var n)) => safe_pos_neg p (var n) *)
  all: try solve [apply spn_var].
  (* nu_abs: safe_pos_neg p (abs T e) => safe_pos_neg p (abs (tsubst A 0 T) (nu K A e)) *)
  all: try solve [
    match goal with H: safe_pos_neg _ (abs _ _) |- safe_pos_neg _ (abs _ (nu _ _ _)) =>
      inversion H; subst; clear H;
      apply spn_abs; apply spn_nu; assumption
    end].
  (* nu_tabs: safe_pos_neg p (tabs L e) => safe_pos_neg p (tabs L (nu K (tlift 1 0 A) (term_tswap 0 e))) *)
  all: try solve [
    match goal with H: safe_pos_neg _ (tabs _ _) |- safe_pos_neg _ (tabs _ (nu _ _ _)) =>
      inversion H; subst; clear H;
      apply spn_tabs; apply spn_nu; apply safe_pos_neg_term_tswap; assumption
    end].
  (* nu_gnd: safe_pos_neg p (gnd v G) => safe_pos_neg p (gnd (nu K A v) (tsubst A 0 G)) *)
  all: try solve [
    match goal with H: safe_pos_neg _ (gnd _ _) |- safe_pos_neg _ (gnd (nu _ _ _) _) =>
      inversion H; subst; clear H;
      apply spn_gnd; apply spn_nu; assumption
    end].
  (* nu_tamper: safe_pos_neg p (nu K A (gnd v (tvar 0))) => safe_pos_neg p (blame (mk_label 0 true)) *)
  all: try solve [apply spn_blame; apply label_id_neq; simpl; lia].
  (* nu_congr: safe_pos_neg p (nu K A e), e ~> e' => safe_pos_neg p (nu K A e') *)
  all: try solve [
    match goal with H: safe_pos_neg _ (nu _ _ _) |- _ =>
      inversion H; subst; clear H; apply spn_nu; auto
    end].
  (* nu_blame: safe_pos_neg p (nu K A (blame q)) => safe_pos_neg p (blame q) *)
  all: try solve [
    match goal with H: safe_pos_neg _ (nu _ _ _) |- _ =>
      inversion H; subst; clear H;
      match goal with H2: safe_pos_neg _ (blame _) |- _ =>
        inversion H2; subst; apply spn_blame; assumption
      end
    end].
  all: try solve [
    match goal with H: safe_pos_neg _ (nu _ _ _) |- _ =>
      inversion H; subst; clear H; auto
    end].
  (* GROUND (via [ground_tag]), positive: [ground_tag_pos] gives the inner evidence *)
  all: try solve [
    apply spn_gnd; apply spn_cast_pos; [apply ground_tag_pos; assumption | assumption]].
  (* GROUND, negative: [neg_subtype_ground_tag_from_dyn] from the outer [A <:- ?] *)
  all: try solve [
    apply spn_gnd; apply spn_cast_neg;
      [eapply neg_subtype_ground_tag_from_dyn; eassumption | assumption]].
  (* COLLAPSE, positive: ground-restricted [?]-universality *)
  all: try solve [
    match goal with Hspn: safe_pos_neg _ (gnd _ _) |- safe_pos_neg _ (cast _ _ _ _) =>
      inversion Hspn; subst; clear Hspn;
      apply spn_cast_pos; [apply pos_subtype_dyn_ground; assumption | assumption]
    end].
  (* ALL/ALL structural cast under the binder: positive / negative / other label *)
  all: try solve [
    apply spn_tabs; apply spn_cast_pos;
      [ eapply pos_subtype_all_cong_inv; eassumption
      | apply spn_tapp; apply safe_pos_neg_term_tlift; assumption ]].
  all: try solve [
    apply spn_tabs; apply spn_cast_neg;
      [ eapply neg_subtype_all_cong_inv; eassumption
      | apply spn_tapp; apply safe_pos_neg_term_tlift; assumption ]].
  all: try solve [
    apply spn_tabs; apply spn_cast_other;
      [ assumption
      | apply spn_tapp; apply safe_pos_neg_term_tlift; assumption ]].
Qed.

(** Multi-step preservation of [safe_pos_neg]. *)
Lemma blame_preservation_star:
  forall s s' p,
  lbl_id p >= 2 ->
  safe_pos_neg p s -> [s ~>* s'] -> safe_pos_neg p s'.
Proof.
  intros s s' p Hid Hsafe Hstar. induction Hstar; eauto.
  eapply blame_preservation; eauto.
Qed.

(** ** Blame Progress *)

(** A single step from a safe term never produces [blame p]. *)
Lemma blame_progress:
  forall s p,
  lbl_id p >= 2 ->
  safe_pos_neg p s -> forall s', [s ~> s'] -> s' <> blame p.
Proof.
  intros s p Hid Hsafe s' Hstep.
  apply safe_pos_neg_not_blame.
  exact (blame_preservation _ _ _ Hid Hsafe Hstep).
Qed.

(** ** Blame Theorem *)

(** Theorem 14: a [safe_pos_neg p] term never reduces to [blame p]. *)
Theorem blame_theorem:
  forall s p,
  lbl_id p >= 2 ->
  safe_pos_neg p s ->
  ~ [s ~>* blame p].
Proof.
  intros s p Hid Hsafe Hstar.
  apply (safe_pos_neg_not_blame _ _ (blame_preservation_star _ _ _ Hid Hsafe Hstar) eq_refl).
Qed.

(** Corollary 15: if casts carry positive subtyping evidence, positive blame cannot fire. *)
Corollary blame_theorem_pos:
  forall t A B p,
  lbl_id p >= 2 ->
  safe_pos_neg p t ->
  pos_subtype A B ->
  ~ [t ~>* blame p].
Proof.
  intros. exact (blame_theorem t p H H0).
Qed.
