(** * BlameFOmega.subtyping_safety: Subtyping-label safety.

    Proves that [safe_sub p] is preserved by one-step and multi-step
    reduction.  A term satisfying that syntactic invariant cannot reduce to
    either polarity of the tracked label.  This file does not formalize the
    unique-cast-in-a-program premise of Ahmed et al.'s contextual corollary. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From BlameFOmega Require Import syntax.
From BlameFOmega Require Import infrastructure.
From BlameFOmega Require Import semantics.
From BlameFOmega Require Import subtyping.
From BlameFOmega Require Import safety.

(** ** Subtyping safety: one step never emits tracked blame *)

(** One step from a [safe_sub p] term never produces [blame p] or [blame p̄].
    (This is a single-step no-tracked-blame lemma, not an operational progress
    theorem: it does not assert that a non-value can step.) *)
Lemma safe_sub_step_no_tracked_blame:
  forall s p,
  external_label p ->
  safe_sub p s -> forall s', [s ~> s'] ->
  s' <> blame p /\ s' <> blame (negate p).
Proof.
  intros s p Hid Hsafe s' Hstep.
  unfold external_label, first_external_label_id in Hid.
  revert Hsafe. induction Hstep; intros Hsafe; inversion Hsafe; subst;
  try (split; discriminate).
  all: try solve [split; intro Heq; try discriminate;
    try (injection Heq; intros; subst; simpl in *; try lia;
         try (match goal with H: lbl_id _ <> lbl_id _ |- _ =>
           first [apply H; reflexivity | rewrite negate_id in H; apply H; reflexivity] end);
         try (apply negate_neq in Heq; auto);
         try (symmetry in Heq; apply negate_neq in Heq; auto))].
  all: try solve [split; intro Heq; subst;
    try (match goal with H: value ?v |- _ =>
      first [apply (value_not_blame v p) in H; auto
            | apply (value_not_blame v (negate p)) in H; auto] end)].
  all: try solve [
    match goal with Hss: safe_sub _ _ |- _ =>
      inversion Hss; subst;
      try (split; intro Heq; try discriminate;
        try (injection Heq; intros; subst; simpl in *;
          try (match goal with H: lbl_id _ <> lbl_id _ |- _ =>
            first [apply H; reflexivity | rewrite negate_id in H; apply H; reflexivity] end);
          try lia;
          try (apply negate_neq in Heq; auto);
          try (symmetry in Heq; apply negate_neq in Heq; auto);
          try (match goal with Hss2: safe_sub _ _ |- _ =>
            inversion Hss2; subst;
            try (match goal with H: lbl_id _ <> lbl_id _ |- _ =>
              first [apply H; reflexivity | rewrite negate_id in H; apply H; reflexivity] end) end)))
    end].
  all: try solve [split; discriminate].
  all: try solve [split; intro Heq; injection Heq; intros; subst; simpl in *;
    first [lia | match goal with H: ?x <> ?x |- _ => apply H; reflexivity end
          | match goal with H: negate ?p = ?p |- _ => exact (negate_neq p H) end
          | match goal with H: ?p = negate ?p |- _ => symmetry in H; exact (negate_neq p H) end]].
  all: try solve [split; intro Heq; try discriminate; injection Heq; intros; subst;
    match goal with H: value (blame _) |- _ =>
      exfalso; inversion H end].
  (* Blame propagation: result is blame q where q comes from subterm *)
  all: try solve [
    match goal with Hss: safe_sub _ _ |- _ =>
      inversion Hss; subst;
      split; intro Heq; injection Heq; intros; subst;
      match goal with H: safe_sub _ (blame _) |- _ =>
        inversion H; subst;
        match goal with H2: lbl_id _ <> lbl_id _ |- _ =>
          first [apply H2; reflexivity
                |rewrite negate_id in H2; apply H2; reflexivity]
        end
      end
    end].
  (* Conflict: cast (gnd v G) dyn A p ~> blame p *)
  all: try solve [
    match goal with Hss: safe_sub _ (cast _ _ _ _) |- _ =>
      inversion Hss; subst;
      split; intro Heq; try discriminate; injection Heq; intros; subst;
      simpl in *; try lia;
      try (match goal with H: lbl_id _ <> lbl_id _ |- _ =>
        first [apply H; reflexivity | rewrite negate_id in H; apply H; reflexivity] end)
    end].
  (* Additional: invert twice for nested structures *)
  all: try solve [
    match goal with Hss: safe_sub _ _ |- _ =>
      inversion Hss; subst;
      try (match goal with Hss2: safe_sub _ _ |- _ =>
        inversion Hss2; subst end);
      split; intro Heq; try discriminate; injection Heq; intros; subst;
      simpl in *;
      first [lia
            | match goal with H: lbl_id _ <> lbl_id _ |- _ =>
                first [apply H; reflexivity | rewrite negate_id in H; apply H; reflexivity] end
            | match goal with H: negate _ = _ |- _ => apply negate_neq in H; auto end
            | match goal with H: _ = negate _ |- _ => symmetry in H; apply negate_neq in H; auto end]
    end].
  (* Beta: substitution preserves safe_sub *)
  all: try solve [
    apply safe_sub_not_blame;
    apply safe_sub_subst; [|assumption];
    match goal with H: safe_sub _ (abs _ _) |- _ => inversion H; assumption end].
  (* TBeta: tapp (tabs K b) A ~> nu K A b *)
  all: try solve [
    apply safe_sub_not_blame;
    apply ss_nu;
    match goal with H: safe_sub _ (tapp _ _) |- _ =>
      inversion H; subst; clear H;
      match goal with H2: safe_sub _ (tabs _ _) |- _ =>
        inversion H2; subst; clear H2; assumption
      end
    end].
  (* Conflict: subtype dyn A contradicts ~compat G A *)
  all: try solve [
    exfalso; match goal with
    | Hnc: ~ compat ?G ?A, Hs: subtype dyn ?A |- _ =>
      apply Hnc; apply subtype_dyn_compat; assumption
    end].
  (* tabs_congr *)
  all: try solve [split; discriminate].
  (* tabs_blame *)
  all: try solve [
    match goal with H: safe_sub _ (tabs _ _) |- _ =>
      inversion H; subst; clear H;
      match goal with H2: safe_sub _ (blame _) |- _ =>
        apply safe_sub_not_blame in H2; destruct H2; split; intro; congruence
      end
    end].
  (* nu_var *)
  all: try solve [split; discriminate].
  (* nu_abs *)
  all: try solve [split; discriminate].
  (* nu_tabs *)
  all: try solve [split; discriminate].
  (* nu_gnd *)
  all: try solve [split; discriminate].
  (* nu_tamper: blame (mk_label 0 true) *)
  all: try solve [split; intro Heq; injection Heq; intros; subst; simpl in *; lia].
  (* nu_congr *)
  all: try solve [split; discriminate].
  (* nu_blame *)
  all: try solve [
    match goal with H: safe_sub _ (nu _ _ _) |- _ =>
      inversion H; subst; clear H;
      match goal with H2: safe_sub _ (blame _) |- _ =>
        apply safe_sub_not_blame in H2; destruct H2; split; intro; congruence
      end
    end].
Qed.

(** ** Subtyping Preservation *)

(** One-step preservation of [safe_sub]: if [s] is safe and steps to [s'], so is [s']. *)
Lemma subtyping_preservation:
  forall s s' p,
  external_label p ->
  safe_sub p s -> [s ~> s'] -> safe_sub p s'.
Proof.
  intros s s' p Hid Hsafe Hstep.
  unfold external_label, first_external_label_id in Hid.
  revert Hsafe. induction Hstep; intros Hsafe; inversion Hsafe; subst;
  eauto with blame.
  (* beta *)
  all: try solve [
    apply safe_sub_subst; [| eassumption];
    match goal with H: safe_sub _ (abs _ _) |- _ => inversion H; eassumption end
  ].
  (* tbeta: tapp (tabs K b) A ~> nu K A b *)
  all: try solve [
    apply ss_nu;
    match goal with H: safe_sub _ (tabs _ _) |- _ => inversion H; eassumption end
  ].
  (* tamper: blame with id 0 or 1 *)
  all: try solve [constructor; simpl; lia].
  (* is_true, is_false *)
  all: try solve [repeat constructor].
  (* simple congruence and structural *)
  all: try solve [constructor; auto; try (constructor; auto; try (constructor; auto))].
  (* wrap pos: subtype inversion gives sub_refl and sub_arrow *)
  all: try solve [
    match goal with Hs: subtype _ _ |- _ =>
      inversion Hs; subst; clear Hs;
      [ apply ss_abs;
        first [apply ss_cast_pos; [apply sub_refl |]
              |apply ss_cast_neg; [apply sub_refl |]];
        apply ss_app; [apply safe_sub_lift; eassumption |];
        first [apply ss_cast_neg; [apply sub_refl |]
              |apply ss_cast_pos; [apply sub_refl |]];
        apply ss_var
      | apply ss_abs;
        first [apply ss_cast_pos; [eassumption |]
              |apply ss_cast_neg; [eassumption |]];
        apply ss_app; [apply safe_sub_lift; eassumption |];
        first [apply ss_cast_neg; [eassumption |]
              |apply ss_cast_pos; [eassumption |]];
        apply ss_var ]
    end].
  (* wrap neg: negate(negate p) = p *)
  all: try solve [
    match goal with Hs: subtype _ _ |- _ =>
      inversion Hs; subst; clear Hs;
      [ apply ss_abs; apply ss_cast_neg; [apply sub_refl |];
        apply ss_app; [apply safe_sub_lift; eassumption |];
        rewrite negate_negate; apply ss_cast_pos; [apply sub_refl |]; apply ss_var
      | apply ss_abs; apply ss_cast_neg; [eassumption |];
        apply ss_app; [apply safe_sub_lift; eassumption |];
        rewrite negate_negate; apply ss_cast_pos; [eassumption |]; apply ss_var ]
    end].
  (* wrap other: no subtype hyp, use ss_cast_other *)
  all: try solve [
    apply ss_abs; apply ss_cast_other; [assumption |];
    apply ss_app; [apply safe_sub_lift; eassumption |];
    apply ss_cast_other; [rewrite negate_id; assumption |]; apply ss_var].
  (* ground: derive subtype A G from subtype A dyn *)
  all: try solve [
    apply ss_gnd;
    first [apply ss_cast_pos; [eapply subtype_ground_from_dyn; eassumption | eassumption]
          |apply ss_cast_neg; [eapply subtype_ground_from_dyn; eassumption | eassumption]
          |apply ss_cast_other; [assumption | eassumption]]].
  (* collapse: derive subtype G A from subtype dyn A *)
  all: try solve [
    match goal with H: safe_sub _ (gnd _ _) |- _ =>
      inversion H; subst;
      first [apply ss_cast_pos; [eapply subtype_from_dyn; eassumption | assumption]
            |apply ss_cast_neg; [eapply subtype_from_dyn; eassumption | assumption]
            |apply ss_cast_other; [assumption | assumption]]
    end].
  (* conflict: contradiction — subtype dyn A implies compat G A *)
  all: try solve [
    exfalso; match goal with
    | Hnc: ~ compat _ _, Hs: subtype dyn _ |- _ =>
      apply Hnc; apply subtype_dyn_compat; assumption
    end].
  (* generalize pos/neg *)
  all: try solve [
    apply ss_tabs;
    first [apply ss_cast_pos; [eapply subtype_all_r_inv; eassumption | apply safe_sub_term_tlift; eassumption]
          |apply ss_cast_neg; [eapply subtype_all_r_inv; eassumption | apply safe_sub_term_tlift; eassumption]]].
  (* generalize other *)
  all: try solve [
    apply ss_tabs; apply ss_cast_other; [assumption | apply safe_sub_term_tlift; eassumption]].
  (* instantiate pos/neg *)
  all: try solve [
    first [apply ss_cast_pos; [eapply subtype_all_l_inv; eassumption | apply ss_tapp; eassumption]
          |apply ss_cast_neg; [eapply subtype_all_l_inv; eassumption | apply ss_tapp; eassumption]]].
  (* instantiate other *)
  all: try solve [
    apply ss_cast_other; [first [assumption | rewrite negate_id; assumption] | apply ss_tapp; eassumption]].
  (* blame propagation *)
  all: try solve [
    match goal with H: safe_sub _ _ |- _ =>
      inversion H; subst; clear H;
      constructor; try rewrite negate_id in *; auto
    end].
  (* cast blame propagation *)
  all: try solve [
    match goal with H: safe_sub _ (cast _ _ _ _) |- _ =>
      inversion H; subst; clear H;
      try (match goal with H2: safe_sub _ (blame _) |- _ =>
        inversion H2; subst end);
      constructor; try rewrite negate_id in *; auto
    end].
  (* tabs_congr *)
  all: try solve [
    match goal with H: safe_sub _ (tabs _ _) |- _ =>
      inversion H; subst; clear H; apply ss_tabs; auto
    end].
  (* tabs_blame *)
  all: try solve [
    match goal with H: safe_sub _ (tabs _ _) |- _ =>
      inversion H; subst; clear H;
      match goal with H2: safe_sub _ (blame _) |- _ =>
        inversion H2; subst; constructor; try rewrite negate_id in *; auto
      end
    end].
  (* nu_var *)
  all: try solve [apply ss_var].
  (* nu_abs *)
  all: try solve [
    match goal with H: safe_sub _ (abs _ _) |- safe_sub _ (abs _ (nu _ _ _)) =>
      inversion H; subst; clear H;
      apply ss_abs; apply ss_nu; assumption
    end].
  (* nu_tabs *)
  all: try solve [
    match goal with H: safe_sub _ (tabs _ _) |- safe_sub _ (tabs _ (nu _ _ _)) =>
      inversion H; subst; clear H;
      apply ss_tabs; apply ss_nu; apply safe_sub_term_tswap; assumption
    end].
  (* nu_gnd *)
  all: try solve [
    match goal with H: safe_sub _ (gnd _ _) |- safe_sub _ (gnd (nu _ _ _) _) =>
      inversion H; subst; clear H;
      apply ss_gnd; apply ss_nu; assumption
    end].
  (* nu_tamper: blame (mk_label 0 true) *)
  all: try solve [constructor; simpl; lia].
  (* nu_congr *)
  all: try solve [
    match goal with H: safe_sub _ (nu _ _ _) |- _ =>
      inversion H; subst; clear H; apply ss_nu; auto
    end].
  all: try solve [apply ss_nu; auto].
  (* nu_blame *)
  all: try solve [
    match goal with H: safe_sub _ (nu _ _ _) |- _ =>
      inversion H; subst; clear H;
      match goal with H2: safe_sub _ (blame _) |- _ =>
        inversion H2; subst; constructor; try rewrite negate_id in *; auto
      end
    end].
  all: try solve [
    match goal with H: safe_sub _ (blame _) |- _ =>
      inversion H; subst; constructor; try rewrite negate_id in *; auto
    end].
  (* GROUND (via [ground_tag]): inner cast carries [subtype_ground_tag_from_dyn] *)
  all: try solve [
    apply ss_gnd; apply ss_cast_pos;
      [eapply subtype_ground_tag_from_dyn; eassumption | assumption]].
  all: try solve [
    apply ss_gnd; apply ss_cast_neg;
      [eapply subtype_ground_tag_from_dyn; eassumption | assumption]].
  (* ALL/ALL structural cast under the binder: positive / negative label *)
  all: try solve [
    apply ss_tabs; apply ss_cast_pos;
      [ eapply subtype_all_cong_inv; eassumption
      | apply ss_tapp; apply safe_sub_term_tlift; assumption ]].
  all: try solve [
    apply ss_tabs; apply ss_cast_neg;
      [ eapply subtype_all_cong_inv; eassumption
      | apply ss_tapp; apply safe_sub_term_tlift; assumption ]].
  all: try solve [
    apply ss_tabs; apply ss_cast_other;
      [ assumption
      | apply ss_tapp; apply safe_sub_term_tlift; assumption ]].
Qed.

(** ** Subtyping Preservation (multi-step) *)

(** Multi-step preservation of [safe_sub]. *)
Lemma subtyping_preservation_star:
  forall s s' p,
  external_label p ->
  safe_sub p s -> [s ~>* s'] -> safe_sub p s'.
Proof.
  intros s s' p Hid Hsafe Hstar. induction Hstar; eauto.
  eapply subtyping_preservation; eauto.
Qed.

(** ** Subtyping-label safety theorem *)

(** A [safe_sub p] term never reduces to either polarity of the tracked label. *)
Theorem subtyping_theorem:
  forall t p,
  external_label p ->
  safe_sub p t ->
  ~ [t ~>* blame p] /\ ~ [t ~>* blame (negate p)].
Proof.
  intros t p Hid Hsafe. split; intro Hstar;
    destruct (safe_sub_not_blame _ _ (subtyping_preservation_star _ _ _ Hid Hsafe Hstar));
    auto.
Qed.

(** Direct-cast specialization of [subtyping_theorem]. *)
Corollary subtyping_cast_blame_free : forall t A B p,
  external_label p ->
  subtype A B ->
  safe_sub p t ->
  ~ [cast t A B p ~>* blame p] /\
  ~ [cast t A B p ~>* blame (negate p)].
Proof.
  intros t A B p Hexternal Hsub Hsafe.
  apply subtyping_theorem; [exact Hexternal |].
  apply ss_cast_pos; assumption.
Qed.
