(** * BlameFOmega.preservation: Subject reduction for the target typing.

    Proves preservation for the *full* one-step reduction [step] of
    [semantics.v], for the one typing judgment of the development
    ([typing.v]'s [typing] — kind-regular, with the context-indexed
    definitional equality [defeq] in [typing_conv]):

    [[
    Theorem preservation : forall g e A e',
      wf_ctx g -> typing g e A -> step e e' -> typing g e' A.
    ]]

    ** Why the two [nu] commuting rules are provable here

    An earlier iteration of this development had a permissive typing judgment
    (no [wf_typ] premises, context-free [ty_equiv] conversion) plus a separate
    kind-regular judgment [typing_kr], and preservation held only for [step]
    minus [step_nu_abs]/[step_nu_tabs]: pushing a [nu] binder under an
    [abs]/[tabs] reorders a context binding underneath the moved binder, so a
    term variable's looked-up type silently picks up an extra [tlift 1 0]
    across the interposed [has_def] — and with a context-*free* conversion
    rule, an exactly-pinned annotation elsewhere in the term (e.g. a [cast]'s
    source type) stops matching, a genuine counterexample.

    The unified judgment dissolves that counterexample by design: [nu]'s
    binding is [has_def K A] (the seal together with its payload), and [typing_conv]
    converts with [defeq], whose [deq_def] axiom makes a sealed variable
    definitionally equal to its payload *in that context*.  The reordered
    variable's type [tlift 1 0 (tsubst A 0 T)] is then [defeq] to the original
    annotation [T] ([defeq_reveal_subst]), so the two commuting rules preserve
    typing like every other rule.

    ** Proof technique for the binder swaps

    Neither swap needs a bespoke induction over [typing]:

    - [step_nu_abs] ([typing_swap_type_def]): weaken by the new
      [has_type (tsubst A 0 T)] binding *below* the [has_def]
      ([typing_weaken_term] at prefix depth 1), then substitute [var 0] for
      the old [has_type T] binding ([typing_subst]), converting [var 0]'s
      looked-up type back to [T] via [defeq_reveal_subst_gen].  The composite
      term [subst (var 0) 0 (lift 1 1 e)] is [e] again ([subst_var0_lift]).

    - [step_nu_tabs] ([typing_swap_kind_def]): weaken by a fresh [has_kind L]
      *below* the [has_def] ([typing_weaken_kind] at prefix depth 2), then
      substitute the neutral [tvar 1] for the old, now-shadowed [has_kind L]
      ([typing_tsubst]).  The composite is exactly the adjacent-variable swap:
      [tsubst (tvar 1) k (tlift 1 (S (S k)) t) = tswap k t] ([tswap_encode]).

    All cases are proved with zero admitted goals and no new axioms. *)

From Stdlib Require Import Arith Lia List Relations.
Import ListNotations.
From BlameFOmega Require Import syntax infrastructure semantics
  typing typing_metatheory ty_confluence progress.

(** ** Small conversion helpers *)

(** Turn an accumulated [ty_conv_to] into a genuine [defeq] (the [A = C] case
    needs a kinding witness for [deq_refl]). *)
Lemma ty_conv_to_defeq : forall g A C,
  ty_conv_to g A C -> wf_typ g A KStar -> defeq g A C KStar.
Proof.
  intros g A C [<- | [Hd _]] Hwf; [apply deq_refl; exact Hwf | exact Hd].
Qed.

(** Inversion for variables, through [typing_conv] (the one introduction form
    [progress.v] does not need). *)
Lemma typing_var_inv2 : forall g n C,
  typing g (var n) C ->
  exists t, ty_conv_to g t C /\ lookup_term g n = Some t.
Proof.
  intros g n C H. remember (var n) as tm eqn:Htm.
  induction H; try discriminate.
  - injection Htm as ->. exists t. split; [left; reflexivity | assumption].
  - destruct (IHtyping Htm) as [t0 [Hconv Hlk]].
    exists t0. split; [eapply ty_conv_to_conv; eauto | assumption].
Qed.

(** ** De Bruijn identities for the two binder swaps *)

(** Substituting the variable a [lift 1 (S k)] just skipped is the identity:
    the term-level "weaken then contract" cancellation. *)
Lemma subst_var0_lift : forall e k, subst (var 0) k (lift 1 (S k) e) = e.
Proof.
  induction e; intros k; cbn [lift subst term_tlift]; try (f_equal; auto; fail).
  - (* var n *)
    destruct (le_gt_dec (S k) n); cbn [subst].
    + destruct (lt_eq_lt_dec k (1 + n)) as [[?|?]|?]; try lia.
      f_equal; lia.
    + destruct (lt_eq_lt_dec k n) as [[?|?]|?]; try lia; try reflexivity.
      cbn [lift]. destruct (le_gt_dec 0 0); [f_equal; lia | lia].
Qed.

(** The adjacent type-variable swap is "weaken above the pair, then substitute
    [tvar 1] for the lower binder": [tlift 1 (S (S k))] frees up index
    [S (S k)], and substituting [tvar 1] at [k] sends [k ↦ S k] (via the
    [tlift k 0] in [tsubst]'s variable case) and [S k ↦ k]. *)
Lemma tswap_encode : forall t k,
  tsubst (tvar 1) k (tlift 1 (S (S k)) t) = tswap k t.
Proof.
  induction t; intros k; cbn [tlift tsubst tswap]; try (f_equal; auto; fail).
  - (* tvar n *)
    destruct (le_gt_dec (S (S k)) n); cbn [tsubst].
    + (* n >= S (S k): lifted to 1 + n, substitution decrements back *)
      destruct (lt_eq_lt_dec k (1 + n)) as [[?|?]|?]; try lia.
      destruct (Nat.eq_dec n k); [lia|].
      destruct (Nat.eq_dec n (S k)); [lia|].
      f_equal; lia.
    + destruct (lt_eq_lt_dec k n) as [[?|?]|?].
      * (* k < n < S (S k), so n = S k *)
        destruct (Nat.eq_dec n k); [lia|].
        destruct (Nat.eq_dec n (S k)); [|lia].
        f_equal; lia.
      * (* n = k *)
        destruct (Nat.eq_dec n k); [|lia].
        cbn [tlift]. destruct (le_gt_dec 0 1); [f_equal; lia | lia].
      * (* n < k *)
        destruct (Nat.eq_dec n k); [lia|].
        destruct (Nat.eq_dec n (S k)); [lia|].
        reflexivity.
Qed.

(** Term-level version of [tswap_encode]. *)
Lemma term_tswap_encode : forall e k,
  term_tsubst (tvar 1) k (term_tlift 1 (S (S k)) e) = term_tswap k e.
Proof.
  induction e; intros k; cbn [term_tlift term_tsubst term_tswap];
    f_equal; auto using tswap_encode.
Qed.

(** Substituting under the swap collapses to substituting for the *upper*
    variable: the type-level equation behind [step_nu_tabs]'s result type. *)
Lemma tswap_tsubst : forall t s k,
  tsubst (tlift 1 0 s) k (tswap k t) = tsubst s (S k) t.
Proof.
  induction t; intros s k; cbn [tswap tsubst]; try (f_equal; auto; fail).
  - (* tvar n *)
    destruct (Nat.eq_dec n k).
    + subst. cbn [tsubst].
      destruct (lt_eq_lt_dec k (S k)) as [[?|?]|?]; try lia.
      destruct (lt_eq_lt_dec (S k) k) as [[?|?]|?]; try lia.
      f_equal; lia.
    + destruct (Nat.eq_dec n (S k)).
      * subst. cbn [tsubst].
        destruct (lt_eq_lt_dec k k) as [[?|?]|?]; try lia.
        destruct (lt_eq_lt_dec (S k) (S k)) as [[?|?]|?]; try lia.
        rewrite (tlift_tlift s k 1 0). f_equal; lia.
      * cbn [tsubst].
        destruct (lt_eq_lt_dec k n) as [[?|?]|?];
          destruct (lt_eq_lt_dec (S k) n) as [[?|?]|?]; try lia; reflexivity.
Qed.

(** ** The two binder-swap lemmas *)

(** Swap an adjacent [has_type]/[has_def] pair, moving the term binding's
    stored type out of the seal's scope by substituting the payload.  Composed
    from term weakening and the term substitution lemma; the substituted
    variable's looked-up type is converted back via [defeq_reveal_subst_gen]. *)
Lemma typing_swap_type_def : forall g K A T e B,
  typing (has_type T :: has_def K A :: g) e B ->
  wf_typ (has_def K A :: g) T KStar ->
  typing (has_def K A :: has_type (tsubst A 0 T) :: g) e B.
Proof.
  intros g K A T e B H HwfT.
  (* step 1: insert the new [has_type (tsubst A 0 T)] below the pair *)
  pose proof (typing_weaken_term (has_type T :: has_def K A :: nil) g e B
                (tsubst A 0 T) H) as W.
  simpl in W.
  (* step 2: substitute [var 0] for the old [has_type T] at the top *)
  assert (HwfT' : wf_typ (has_def K A :: has_type (tsubst A 0 T) :: g) T KStar)
    by (apply (wf_typ_weaken_type (has_def K A :: nil) g (tsubst A 0 T) T KStar);
        exact HwfT).
  assert (Hu : typing (has_def K A :: has_type (tsubst A 0 T) :: g) (var 0) T).
  { eapply typing_conv.
    - apply typing_var. simpl. reflexivity.
    - apply deq_sym.
      exact (defeq_reveal_subst_gen nil (has_type (tsubst A 0 T) :: g)
               K A T KStar HwfT').
    - exact HwfT'. }
  pose proof (typing_subst nil (has_def K A :: has_type (tsubst A 0 T) :: g)
                (lift 1 1 e) (var 0) T B W Hu) as Sb.
  simpl in Sb.
  rewrite (subst_var0_lift e 0) in Sb.
  exact Sb.
Qed.

(** Swap an adjacent [has_kind]/[has_def] pair.  Composed from type weakening
    (inserting a fresh [has_kind L] below the pair) and the neutral type
    substitution lemma (substituting [tvar 1] for the old, now-shadowed
    binder); the composite is literally [tswap]/[term_tswap] by
    [tswap_encode]/[term_tswap_encode]. *)
Lemma typing_swap_kind_def : forall g L K A e B,
  typing (has_kind L :: has_def K A :: g) e B ->
  typing (has_def K (tlift 1 0 A) :: has_kind L :: g)
         (term_tswap 0 e) (tswap 0 B).
Proof.
  intros g L K A e B H.
  (* step 1: insert a fresh [has_kind L] below the pair *)
  pose proof (typing_weaken_kind (has_kind L :: has_def K A :: nil) g e B L H) as W.
  simpl in W.
  (* step 2: substitute [tvar 1] for the (old) top [has_kind L] *)
  assert (Hs : wf_typ (has_def K (tlift 1 0 A) :: has_kind L :: g) (tvar 1) L)
    by (apply wf_tvar; reflexivity).
  pose proof (typing_tsubst nil (has_def K (tlift 1 0 A) :: has_kind L :: g)
                (term_tlift 1 2 e) (tvar 1) L (tlift 1 2 B) W Hs
                (neutral_tvar 1)) as T.
  simpl in T.
  rewrite (term_tswap_encode e 0) in T.
  rewrite (tswap_encode B 0) in T.
  exact T.
Qed.

(** ** Eliminating a [has_def] binding from [defeq] by its own payload

    [defeq_def_tsubst]: substituting a seal's payload for the sealed variable
    preserves [defeq] — the type-level content of [nu]-elimination.  Mirrors
    [typing_metatheory.defeq_tsubst] (which eliminates a [has_kind] binding
    by an arbitrary type); here the substituted type is the binding's own
    payload, so the [deq_def] case at the vacated index closes by
    [tlift]/[tsubst] cancellation instead of being vacuous. *)

Lemma wf_typ_def_tsubst : forall G1 g K A X J,
  wf_typ (G1 ++ has_def K A :: g) X J -> wf_typ g A K ->
  wf_typ (tsubst_ctx A G1 ++ g) (tsubst A (ntype G1) X) J.
Proof.
  intros G1 g K A X J H HA.
  eapply wf_typ_tsubst; eauto.
  eapply wf_typ_def_to_kind; eauto.
Qed.

(** [lookup_def] transport for removing the [has_def K A] binding at
    [ntype G1]: the new context's entry at [n] is the old entry at
    [sh (ntype G1) n] with [A] substituted in its payload (the [has_def]
    sibling of [typing_metatheory.lookup_def_tsubst]). *)
Lemma lookup_def_def_tsubst : forall G1 g K A n,
  lookup_def (tsubst_ctx A G1 ++ g) n
    = match lookup_def (G1 ++ has_def K A :: g) (sh (ntype G1) n) with
      | None => None
      | Some (K', X) => Some (K', tsubst A (ntype G1) X)
      end.
Proof.
  induction G1 as [|b G1 IH]; intros g K A n; simpl.
  - unfold sh; simpl.
    destruct (lookup_def g n) as [[K' X]|]; simpl; [| reflexivity].
    f_equal. f_equal. symmetry. apply tsubst_tlift_cancel.
  - destruct b as [D | K' | K' D]; simpl.
    + apply IH.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * reflexivity.
      * specialize (IH g K A n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; rewrite IH;
          destruct (lookup_def (G1 ++ has_def K A :: g) _) as [[K'' X]|]; simpl;
          try reflexivity;
          f_equal; f_equal;
          rewrite (commute_tlift_tsubst_rec X A 1 (ntype G1) 0) by lia;
          reflexivity.
    + unfold sh; simpl. destruct n as [|n']; simpl.
      * f_equal; f_equal.
        rewrite (commute_tlift_tsubst_rec D A 1 (ntype G1) 0) by lia.
        reflexivity.
      * specialize (IH g K A n'). unfold sh in IH.
        destruct (le_gt_dec (ntype G1) n') eqn:E; simpl; rewrite IH;
          destruct (lookup_def (G1 ++ has_def K A :: g) _) as [[K'' X]|]; simpl;
          try reflexivity;
          f_equal; f_equal;
          rewrite (commute_tlift_tsubst_rec X A 1 (ntype G1) 0) by lia;
          reflexivity.
Qed.

Lemma defeq_def_tsubst : forall G1 g Kv A X Y J,
  defeq (G1 ++ has_def Kv A :: g) X Y J ->
  wf_typ g A Kv ->
  defeq (tsubst_ctx A G1 ++ g) (tsubst A (ntype G1) X) (tsubst A (ntype G1) Y) J.
Proof.
  intros G1 g Kv A X Y J H HA.
  remember (G1 ++ has_def Kv A :: g) as g0 eqn:Hg. revert G1 Hg.
  induction H; intros G1 Hg; subst.
  - apply deq_refl. eapply wf_typ_def_tsubst; eauto.
  - apply deq_sym. apply IHdefeq. reflexivity.
  - eapply deq_trans; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - apply deq_ty_equiv;
      [ eapply wf_typ_def_tsubst; eauto
      | eapply wf_typ_def_tsubst; eauto
      | apply ty_equiv_tsubst; auto ].
  - (* deq_def *)
    assert (Hwf' : wf_typ (tsubst_ctx A G1 ++ g) (tsubst A (ntype G1) (tvar n)) K)
      by (eapply wf_typ_def_tsubst; eauto).
    destruct (lt_eq_lt_dec (ntype G1) n) as [[Hlt|Heq]|Hgt].
    + (* n > ntype G1: entry from [g], found at [pred n] after removal *)
      rewrite (tsubst_ref_gt A n (ntype G1)) by lia.
      rewrite (tsubst_ref_gt A n (ntype G1)) in Hwf' by lia.
      eapply deq_def; [| exact Hwf'].
      rewrite (lookup_def_def_tsubst G1 g Kv A (pred n)).
      unfold sh. destruct (le_gt_dec (ntype G1) (pred n)); [| lia].
      replace (S (pred n)) with n by lia. rewrite H. reflexivity.
    + (* n = ntype G1: the vacated seal itself — payload substitution cancels *)
      subst n. rewrite lookup_def_self in H.
      injection H as <- <-.
      rewrite tsubst_ref_eq.
      rewrite (simplify_tsubst_rec A A (ntype G1) (ntype G1) 0) by lia.
      apply deq_refl. apply wf_typ_weaken_tsubst_prefix. exact HA.
    + (* n < ntype G1: entry from [G1], payload substituted *)
      rewrite (tsubst_ref_lt A n (ntype G1)) by lia.
      rewrite (tsubst_ref_lt A n (ntype G1)) in Hwf' by lia.
      eapply deq_def; [| exact Hwf'].
      rewrite (lookup_def_def_tsubst G1 g Kv A n).
      unfold sh. destruct (le_gt_dec (ntype G1) n); [lia |].
      rewrite H. reflexivity.
  - simpl. apply deq_arrow; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
  - simpl. apply deq_all. apply (IHdefeq (has_kind K :: G1)). reflexivity.
  - simpl. apply deq_tyabs. apply (IHdefeq (has_kind K1 :: G1)). reflexivity.
  - simpl. eapply deq_tyapp; [apply IHdefeq1 | apply IHdefeq2]; reflexivity.
Qed.

(** ** [ground]/[neutral] preservation when the substituted variable is absent

    [step_nu_gnd]'s [tvar_occurs 0 G = false] guard means substitution at 0 is
    a pure index shift, so no [neutral]ity of the payload is needed. *)
Lemma neutral_tsubst_shift : forall N s,
  neutral N -> tvar_occurs 0 N = false -> neutral (tsubst s 0 N).
Proof.
  induction 1; intros Hocc; simpl in *.
  - destruct n as [ | n' ].
    + simpl in Hocc. discriminate.
    + apply neutral_tvar.
  - apply Bool.orb_false_iff in Hocc as [HF HA].
    apply neutral_tyapp. apply IHneutral. exact HF.
Qed.

Lemma ground_tsubst_shift : forall G s,
  ground G -> tvar_occurs 0 G = false -> ground (tsubst s 0 G).
Proof.
  intros G s Hg Hocc; inversion Hg; subst; simpl.
  - apply ground_arrow.
  - apply ground_neutral. apply neutral_tsubst_shift; assumption.
Qed.

(** ** [compat] inversion helpers for the three ∀-cast rules
    ([step_generalize], [step_instantiate], [step_all_all]): each rule's
    guards pin down exactly one of [compat]'s seven constructors. *)
Lemma compat_generalize_inv : forall A K C,
  A <> dyn -> (forall K' C', A <> all K' C') ->
  compat A (all K C) -> compat (tlift 1 0 A) C.
Proof.
  intros A K C Hnd Hna Hc.
  inversion Hc as [A0 | A1 A2 B1 B2 Hc1 Hc2 | K0 A0 B0 Hc0 | A0 K0 B0 Hd Hforall Hc0
                   | A0 B0 Hforall Hc0 | A0 G0 Hd Hforall Hgt Hc0 | B0 Hd Hcf];
    subst; try discriminate.
  - exfalso; eapply Hna; reflexivity.
  - exfalso; eapply Hna; reflexivity.
  - assumption.
  - exfalso; eapply Hna; reflexivity.
  - exfalso; eapply Hnd; reflexivity.
Qed.

Lemma compat_instantiate_inv : forall A B,
  (forall K' B', B <> all K' B') ->
  compat (all KStar A) B -> compat (tsubst dyn 0 A) B.
Proof.
  intros A B Hnb Hc.
  inversion Hc as [A0 | A1 A2 B1 B2 Hc1 Hc2 | K0 A0 B0 Hc0 | A0 K0 B0 Hd Hforall Hc0
                   | A0 B0 Hforall Hc0 | A0 G0 Hd Hforall Hgt Hc0 | B0 Hd Hcf];
    subst; try discriminate.
  - exfalso; eapply Hnb; reflexivity.
  - exfalso; eapply Hnb; reflexivity.
  - exfalso; eapply Hnb; reflexivity.
  - assumption.
  - exfalso; eapply (Hforall KStar A); reflexivity.
Qed.

(** Instantiating a type freshly weakened one binder up, at the very
    variable that weakening just introduced, is the identity. Needed for
    [step_all_all]'s eta-style reconstruction [tapp (tlift v) (tvar 0)]. *)
Lemma tsubst_tvar0_tlift_gen : forall A k,
  tsubst (tvar 0) k (tlift 1 (S k) A) = A.
Proof.
  induction A; intros k.
  - unfold tlift; fold tlift.
    destruct (le_gt_dec (S k) n) as [Hge | Hlt];
      unfold tsubst; fold tsubst.
    + destruct (lt_eq_lt_dec k (1 + n)) as [[Hlt2 | Heq2] | Hgt2];
        simpl; try (exfalso; lia); f_equal; lia.
    + destruct (lt_eq_lt_dec k n) as [[Hlt2 | Heq2] | Hgt2];
        simpl; try (exfalso; lia); try reflexivity.
      subst. f_equal. lia.
  - simpl. f_equal; auto.
  - simpl. f_equal. apply IHA.
  - simpl. f_equal. apply IHA.
  - simpl. f_equal; auto.
  - reflexivity.
Qed.

Corollary tsubst_tvar0_tlift1 : forall A, tsubst (tvar 0) 0 (tlift 1 1 A) = A.
Proof. intros A. exact (tsubst_tvar0_tlift_gen A 0). Qed.

Lemma compat_all_inv : forall K A B,
  A <> B -> compat (all K A) (all K B) -> compat A B.
Proof.
  intros K A B Hne Hc.
  inversion Hc as [A0 | A1 A2 B1 B2 Hc1 Hc2 | K0 A0 B0 Hc0 | A0 K0 B0 Hd Hforall Hc0
                   | A0 B0 Hforall Hc0 | A0 G0 Hd Hforall Hgt Hc0 | B0 Hd Hcf];
    subst; try discriminate.
  - exfalso; apply Hne; reflexivity.
  - assumption.
  - exfalso; eapply Hforall; reflexivity.
  - exfalso; eapply Hforall; reflexivity.
Qed.

(** ** The preservation theorem *)

Theorem preservation : forall g e A e',
  wf_ctx g -> typing g e A -> step e e' -> typing g e' A.
Proof.
  intros g e A e' Hwf Hty Hstep. revert g A Hwf Hty.
  induction Hstep; intros g Aout Hwf Hty.

  - (* step_beta *)
    rename t into t1, b into body, x into x0.
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_app_inv2 in Hty. destruct Hty as [A0 [B0 [Hconv [Htyf Htyx]]]].
    apply typing_abs_inv2 in Htyf. destruct Htyf as [B1 [Hconv2 [Htybody Hwft1]]].
    assert (HwfB1 : wf_typ g B1 KStar).
    { apply (wf_typ_strengthen_type nil g t1 B1 KStar).
      exact (typing_regular _ _ _ (wf_ctx_type g t1 Hwf Hwft1) Htybody). }
    assert (Hd : defeq g (arrow t1 B1) (arrow A0 B0) KStar)
      by (apply ty_conv_to_defeq; [exact Hconv2 | apply wf_arrow; assumption]).
    destruct (defeq_arrow_inv g t1 B1 A0 B0 Hwf Hd) as [HeqDom HeqCod].
    assert (Htyx' : typing g x0 t1)
      by (eapply typing_conv; [exact Htyx | apply deq_sym; exact HeqDom | exact Hwft1]).
    pose proof (typing_subst0 g body x0 t1 B1 Htybody Htyx') as Hsub.
    assert (HwfB0 : wf_typ g B0 KStar).
    { pose proof (defeq_regular_r g _ _ _ Hwf Hd) as W. inversion W; subst; assumption. }
    eapply apply_ty_conv_to; [| exact Hconv].
    eapply typing_conv; [exact Hsub | exact HeqCod | exact HwfB0].

  - (* step_tbeta *)
    rename b into body.
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_tapp_inv2 in Hty. destruct Hty as [K1 [t1 [Hconv [Htyf Hwft]]]].
    apply typing_tabs_inv2 in Htyf. destruct Htyf as [B1 [Hconv2 Htybody]].
    assert (HwfB1 : wf_typ (has_kind K :: g) B1 KStar)
      by (exact (typing_regular _ _ _ (wf_ctx_kind g K Hwf) Htybody)).
    assert (Hd : defeq g (all K B1) (all K1 t1) KStar)
      by (apply ty_conv_to_defeq; [exact Hconv2 | apply wf_all; exact HwfB1]).
    destruct (defeq_all_inv g K B1 K1 t1 Hwf Hd) as [-> HeqB].
    pose proof (typing_kind_to_def nil g K1 t body B1 Htybody) as Htybody'.
    simpl in Htybody'.
    assert (Hnu : typing g (nu K1 t body) (tsubst t 0 B1))
      by (apply typing_nu; assumption).
    assert (Hd2 : defeq g (tsubst t 0 B1) (tsubst t 0 t1) KStar).
    { pose proof (defeq_tsubst nil g K1 t B1 t1 KStar HeqB Hwft) as P.
      simpl in P. exact P. }
    assert (HwfSub : wf_typ g (tsubst t 0 t1) KStar)
      by (eapply defeq_regular_r; eauto).
    eapply apply_ty_conv_to; [| exact Hconv].
    eapply typing_conv; [exact Hnu | exact Hd2 | exact HwfSub].

  - (* step_wrap *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfArrAB HwfArrAB']]]].
    inversion HwfArrAB as [ | HwfA HwfB | | | | ]; subst.
    inversion HwfArrAB' as [ | HwfA' HwfB' | | | | ]; subst.
    apply compat_arrow_inv in Hcomp. destruct Hcomp as [HcompA'A HcompBB'].
    assert (HwfA0 : wf_typ (has_type A' :: g) A KStar)
      by (apply (wf_typ_weaken_type nil g A' A KStar); auto).
    assert (HwfB0 : wf_typ (has_type A' :: g) B KStar)
      by (apply (wf_typ_weaken_type nil g A' B KStar); auto).
    assert (HwfB'0 : wf_typ (has_type A' :: g) B' KStar)
      by (apply (wf_typ_weaken_type nil g A' B' KStar); auto).
    assert (HwfA'0 : wf_typ (has_type A' :: g) A' KStar)
      by (apply (wf_typ_weaken_type nil g A' A' KStar); auto).
    assert (Hv0 : typing (has_type A' :: g) (lift 1 0 v) (arrow A B))
      by (apply typing_weaken_term0; exact Htyv).
    assert (Hvar0 : typing (has_type A' :: g) (var 0) A')
      by (apply typing_var; reflexivity).
    assert (Hcastvar : typing (has_type A' :: g) (cast (var 0) A' A (negate p)) A)
      by (eapply typing_cast; eauto).
    assert (Happ : typing (has_type A' :: g)
              (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B)
      by (eapply typing_app; eauto).
    assert (Hcastapp : typing (has_type A' :: g)
              (cast (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B B' p) B')
      by (eapply typing_cast; eauto).
    assert (Habs : typing g
              (abs A' (cast (app (lift 1 0 v) (cast (var 0) A' A (negate p))) B B' p))
              (arrow A' B'))
      by (apply typing_abs; auto).
    eapply apply_ty_conv_to; eauto.

  - (* step_id *)
    apply typing_cast_inv2 in Hty. destruct Hty as [Hconv [Htyv _]].
    eapply apply_ty_conv_to; eauto.

  - (* step_ground *)
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfA _]]]].
    assert (HwfG : wf_typ g G KStar).
    { inversion H2 as [A0 B0 | N HN]; subst.
      - apply wf_arrow; apply wf_dyn.
      - exfalso; apply H4; reflexivity. }
    assert (Hcast : typing g (cast v A G p) G)
      by (eapply typing_cast; eauto).
    assert (Hgnd : typing g (gnd (cast v A G p) G) dyn)
      by (apply typing_gnd; eauto using ground_tag_ground with blame).
    eapply apply_ty_conv_to; eauto.

  - (* step_ground_id *)
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [_ [HwfG _]]]].
    assert (Hgnd : typing g (gnd v G) dyn)
      by (apply typing_gnd; auto with blame).
    eapply apply_ty_conv_to; eauto.

  - (* step_collapse *)
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htygnd [_ [_ HwfA]]]].
    apply (typing_gnd_inv2 g v G dyn) in Htygnd.
    destruct Htygnd as [_ [Htyv [_ HwfG]]].
    assert (Hcast : typing g (cast v G A p) A)
      by (eapply typing_cast; eauto).
    eapply apply_ty_conv_to; eauto.

  - (* step_conflict *)
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [_ [_ [_ HwfA]]]].
    assert (Hblame : typing g (blame p) A) by (apply typing_blame; exact HwfA).
    eapply apply_ty_conv_to; eauto.

  - (* step_is_true *)
    apply typing_is_gnd_inv2 in Hty. destruct Hty as [Hconv _].
    assert (Habs : typing g (abs dyn (abs dyn (var 1))) (arrow dyn (arrow dyn dyn))).
    { apply typing_abs; [apply wf_dyn |]. apply typing_abs; [apply wf_dyn |].
      apply typing_var. reflexivity. }
    eapply apply_ty_conv_to; eauto.

  - (* step_is_false *)
    apply typing_is_gnd_inv2 in Hty. destruct Hty as [Hconv _].
    assert (Habs : typing g (abs dyn (abs dyn (var 0))) (arrow dyn (arrow dyn dyn))).
    { apply typing_abs; [apply wf_dyn |]. apply typing_abs; [apply wf_dyn |].
      apply typing_var. reflexivity. }
    eapply apply_ty_conv_to; eauto.

  - (* step_is_tamper *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_tabs_congr *)
    apply typing_tabs_inv2 in Hty. destruct Hty as [B [Hconv Hbody]].
    assert (Hbody' : typing (has_kind K :: g) e' B)
      by (apply (IHHstep (has_kind K :: g) B); [constructor; assumption | exact Hbody]).
    assert (Htabs : typing g (tabs K e') (all K B)) by (apply typing_tabs; exact Hbody').
    eapply apply_ty_conv_to; eauto.

  - (* step_tabs_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_nu_var *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htybody HwfA]]].
    apply typing_var_inv2 in Htybody. destruct Htybody as [t [Hconv2 Hlk]].
    simpl in Hlk.
    case_eq (lookup_term g n); [intros t0 Hlk0 | intros Hlk0]; rewrite Hlk0 in Hlk;
      simpl in Hlk; try discriminate.
    injection Hlk as <-.
    assert (Hvar : typing g (var n) t0) by (apply typing_var; exact Hlk0).
    destruct Hconv2 as [Heq | [Hdq HwfB]].
    + subst B. rewrite tsubst_tlift_cancel in Hconv.
      eapply apply_ty_conv_to; eauto.
    + pose proof (defeq_def_tsubst nil g K A _ _ KStar Hdq HwfA) as Hd3.
      simpl in Hd3. rewrite tsubst_tlift_cancel in Hd3.
      assert (HwfSub : wf_typ g (tsubst A 0 B) KStar)
        by (eapply defeq_regular_r; eauto).
      eapply apply_ty_conv_to; [| exact Hconv].
      eapply typing_conv; [exact Hvar | exact Hd3 | exact HwfSub].

  - (* step_nu_abs *)
    rename e into body.
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htyabs HwfA]]].
    apply typing_abs_inv2 in Htyabs. destruct Htyabs as [B1 [Hconv2 [Htybody HwfT]]].
    (* the body, with the [has_type]/[has_def] pair swapped *)
    pose proof (typing_swap_type_def g K A T body B1 Htybody HwfT) as Hbody'.
    assert (HwfTs : wf_typ g (tsubst A 0 T) KStar).
    { pose proof (wf_typ_def_to_kind nil g K A T KStar HwfT) as W.
      exact (wf_typ_tsubst nil g K A T KStar W HwfA). }
    assert (Hnu : typing (has_type (tsubst A 0 T) :: g) (nu K A body) (tsubst A 0 B1)).
    { apply typing_nu; [exact Hbody' |].
      apply (wf_typ_weaken_type nil g (tsubst A 0 T) A K). exact HwfA. }
    assert (Habs : typing g (abs (tsubst A 0 T) (nu K A body))
                     (arrow (tsubst A 0 T) (tsubst A 0 B1)))
      by (apply typing_abs; assumption).
    (* type plumbing: arrow (tsubst A 0 T) (tsubst A 0 B1) = tsubst A 0 (arrow T B1)
       --defeq-- tsubst A 0 B --conv-- Aout *)
    assert (HwfB1 : wf_typ (has_def K A :: g) B1 KStar).
    { apply (wf_typ_strengthen_type nil (has_def K A :: g) T B1 KStar).
      apply (typing_regular _ _ _
               (wf_ctx_type (has_def K A :: g) T (wf_ctx_def g K A Hwf HwfA) HwfT)
               Htybody). }
    assert (Hd2 : defeq (has_def K A :: g) (arrow T B1) B KStar)
      by (apply ty_conv_to_defeq; [exact Hconv2 | apply wf_arrow; assumption]).
    pose proof (defeq_def_tsubst nil g K A (arrow T B1) B KStar Hd2 HwfA) as Hd3.
    simpl in Hd3.
    assert (HwfSub : wf_typ g (tsubst A 0 B) KStar)
      by (eapply defeq_regular_r; eauto).
    eapply apply_ty_conv_to; [| exact Hconv].
    eapply typing_conv; [exact Habs | exact Hd3 | exact HwfSub].

  - (* step_nu_tabs *)
    rename e into body.
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htytabs HwfA]]].
    apply typing_tabs_inv2 in Htytabs. destruct Htytabs as [B1 [Hconv2 Htybody]].
    (* the body, with the [has_kind]/[has_def] pair swapped *)
    pose proof (typing_swap_kind_def g L K A body B1 Htybody) as Hbody'.
    assert (Hnu : typing (has_kind L :: g)
                    (nu K (tlift 1 0 A) (term_tswap 0 body))
                    (tsubst (tlift 1 0 A) 0 (tswap 0 B1))).
    { apply typing_nu; [exact Hbody' |].
      exact (wf_typ_weaken_kind nil g L A K HwfA). }
    rewrite (tswap_tsubst B1 A 0) in Hnu.
    assert (Htabs : typing g (tabs L (nu K (tlift 1 0 A) (term_tswap 0 body)))
                      (all L (tsubst A 1 B1)))
      by (apply typing_tabs; exact Hnu).
    (* type plumbing: all L (tsubst A 1 B1) = tsubst A 0 (all L B1)
       --defeq-- tsubst A 0 B --conv-- Aout *)
    assert (HwfB1 : wf_typ (has_kind L :: has_def K A :: g) B1 KStar)
      by (exact (typing_regular _ _ _
                   (wf_ctx_kind (has_def K A :: g) L (wf_ctx_def g K A Hwf HwfA))
                   Htybody)).
    assert (Hd2 : defeq (has_def K A :: g) (all L B1) B KStar)
      by (apply ty_conv_to_defeq; [exact Hconv2 | apply wf_all; exact HwfB1]).
    pose proof (defeq_def_tsubst nil g K A (all L B1) B KStar Hd2 HwfA) as Hd3.
    simpl in Hd3.
    assert (HwfSub : wf_typ g (tsubst A 0 B) KStar)
      by (eapply defeq_regular_r; eauto).
    eapply apply_ty_conv_to; [| exact Hconv].
    eapply typing_conv; [exact Htabs | exact Hd3 | exact HwfSub].

  - (* step_nu_gnd *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htybody HwfA]]].
    apply typing_gnd_inv2 in Htybody. destruct Htybody as [Hconv2 [Htyv [Hg HwfG]]].
    assert (Hnu : typing g (nu K A v) (tsubst A 0 G)) by (apply typing_nu; assumption).
    assert (HwfG' : wf_typ g (tsubst A 0 G) KStar).
    { pose proof (wf_typ_def_to_kind nil g K A G KStar HwfG) as W.
      exact (wf_typ_tsubst nil g K A G KStar W HwfA). }
    assert (Hground' : ground (tsubst A 0 G)) by (apply ground_tsubst_shift; assumption).
    assert (Hgnd : typing g (gnd (nu K A v) (tsubst A 0 G)) dyn)
      by (apply typing_gnd; [assumption | constructor; assumption]).
    destruct Hconv2 as [Heq | [Hdq HwfB]].
    + subst B. simpl in Hconv. eapply apply_ty_conv_to; eauto.
    + pose proof (defeq_def_tsubst nil g K A dyn B KStar Hdq HwfA) as Hd3.
      simpl in Hd3.
      assert (HwfSub : wf_typ g (tsubst A 0 B) KStar)
        by (eapply defeq_regular_r; eauto).
      eapply apply_ty_conv_to; [| exact Hconv].
      eapply typing_conv; [exact Hgnd | exact Hd3 | exact HwfSub].

  - (* step_nu_tamper *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_nu_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_nu_inv2 in Hty. destruct Hty as [B [Hconv [Htybody Hwft]]].
    assert (Htybody' : typing (has_def K A :: g) e' B)
      by (apply (IHHstep (has_def K A :: g) B); [constructor; assumption | exact Htybody]).
    assert (Hnu : typing g (nu K A e') (tsubst A 0 B)) by (apply typing_nu; assumption).
    eapply apply_ty_conv_to; eauto.

  - (* step_nu_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_generalize *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfA HwfAllKB]]]].
    inversion HwfAllKB as [ | | HwfB | | | ]; subst.
    assert (Hcompgen : compat (tlift 1 0 A) B)
      by (apply (compat_generalize_inv A K B); assumption).
    assert (Hv' : typing (has_kind K :: g) (term_tlift 1 0 v) (tlift 1 0 A))
      by (apply typing_weaken_kind0; exact Htyv).
    assert (HwfA' : wf_typ (has_kind K :: g) (tlift 1 0 A) KStar)
      by (apply (wf_typ_weaken_kind nil g K A KStar); exact HwfA).
    assert (Hcast' : typing (has_kind K :: g)
              (cast (term_tlift 1 0 v) (tlift 1 0 A) B p) B)
      by (eapply typing_cast; eauto).
    assert (Htabs : typing g (tabs K (cast (term_tlift 1 0 v) (tlift 1 0 A) B p))
              (all K B))
      by (apply typing_tabs; exact Hcast').
    eapply apply_ty_conv_to; eauto.

  - (* step_instantiate *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfAllA HwfB]]]].
    inversion HwfAllA as [ | | HwfA0 | | | ]; subst.
    assert (Hcompinst : compat (tsubst dyn 0 A) B)
      by (apply compat_instantiate_inv; assumption).
    assert (Htapp : typing g (tapp v dyn) (tsubst dyn 0 A))
      by (eapply typing_tapp; [exact Htyv | apply wf_dyn]).
    assert (HwfAsub : wf_typ g (tsubst dyn 0 A) KStar).
    { pose proof (wf_typ_tsubst nil g KStar dyn A KStar) as P.
      simpl in P. apply P; [assumption | apply wf_dyn]. }
    assert (Hcast' : typing g (cast (tapp v dyn) (tsubst dyn 0 A) B p) B)
      by (eapply typing_cast; eauto).
    eapply apply_ty_conv_to; eauto.

  - (* step_all_all *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_cast_inv2 in Hty.
    destruct Hty as [Hconv [Htyv [Hcomp [HwfAllA HwfAllB]]]].
    inversion HwfAllA as [ | | HwfA | | | ]; subst.
    inversion HwfAllB as [ | | HwfB | | | ]; subst.
    assert (Hcompab : compat A B) by (apply (compat_all_inv K A B); assumption).
    assert (Hv' : typing (has_kind K :: g) (term_tlift 1 0 v) (all K (tlift 1 1 A))).
    { pose proof (typing_weaken_kind0 g v (all K A) K Htyv) as Hw. simpl in Hw. exact Hw. }
    assert (Happ : typing (has_kind K :: g) (tapp (term_tlift 1 0 v) (tvar 0)) A).
    { assert (Hwf0 : wf_typ (has_kind K :: g) (tvar 0) K)
        by (apply wf_tvar; reflexivity).
      pose proof (typing_tapp (has_kind K :: g) (term_tlift 1 0 v)
                    (tlift 1 1 A) (tvar 0) K Hv' Hwf0) as Htp.
      rewrite tsubst_tvar0_tlift1 in Htp. exact Htp. }
    assert (Hcast' : typing (has_kind K :: g)
              (cast (tapp (term_tlift 1 0 v) (tvar 0)) A B p) B)
      by (eapply typing_cast; eauto).
    assert (Htabs : typing g (tabs K (cast (tapp (term_tlift 1 0 v) (tvar 0)) A B p))
              (all K B))
      by (apply typing_tabs; exact Hcast').
    eapply apply_ty_conv_to; eauto.

  - (* step_app_left *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_app_inv2 in Hty. destruct Hty as [A0 [B0 [Hconv [Hty1 Hty2]]]].
    assert (Hty1' : typing g e2 (arrow A0 B0))
      by (apply (IHHstep g (arrow A0 B0)); [exact Hwf | exact Hty1]).
    assert (Happ : typing g (app e2 x) B0) by (eapply typing_app; eauto).
    eapply apply_ty_conv_to; eauto.

  - (* step_app_right *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_app_inv2 in Hty. destruct Hty as [A0 [B0 [Hconv [Hty1 Hty2]]]].
    assert (Hty2' : typing g x2 A0)
      by (apply (IHHstep g A0); [exact Hwf | exact Hty2]).
    assert (Happ : typing g (app v x2) B0) by (eapply typing_app; eauto).
    eapply apply_ty_conv_to; eauto.

  - (* step_tapp_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_tapp_inv2 in Hty. destruct Hty as [K0 [t0 [Hconv [Hty1 Hwft]]]].
    assert (Hty1' : typing g e2 (all K0 t0))
      by (apply (IHHstep g (all K0 t0)); [exact Hwf | exact Hty1]).
    assert (Htapp : typing g (tapp e2 t) (tsubst t 0 t0))
      by (eapply typing_tapp; eauto).
    eapply apply_ty_conv_to; eauto.

  - (* step_cast_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_cast_inv2 in Hty. destruct Hty as [Hconv [Hty1 [Hcomp [HwfA HwfB]]]].
    assert (Hty1' : typing g e2 A) by (apply (IHHstep g A); [exact Hwf | exact Hty1]).
    assert (Hcast' : typing g (cast e2 A B p) B) by (eapply typing_cast; eauto).
    eapply apply_ty_conv_to; eauto.

  - (* step_gnd_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_gnd_inv2 in Hty. destruct Hty as [Hconv [Hty1 [Hg HwfG]]].
    assert (Hty1' : typing g e2 G) by (apply (IHHstep g G); [exact Hwf | exact Hty1]).
    assert (Hgnd' : typing g (gnd e2 G) dyn)
      by (apply typing_gnd; [exact Hty1' | constructor; assumption]).
    eapply apply_ty_conv_to; eauto.

  - (* step_is_gnd_congr *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_is_gnd_inv2 in Hty. destruct Hty as [Hconv Hty1].
    assert (Hty1' : typing g e2 dyn) by (apply (IHHstep g dyn); [exact Hwf | exact Hty1]).
    assert (Hisgnd' : typing g (is_gnd e2 G) (arrow dyn (arrow dyn dyn)))
      by (apply typing_is_gnd; exact Hty1').
    eapply apply_ty_conv_to; eauto.

  - (* step_app_blame_l *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_app_blame_r *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_tapp_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_cast_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_gnd_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.

  - (* step_is_gnd_blame *)
    pose proof (typing_regular g _ Aout Hwf Hty) as HwfAout.
    apply typing_blame. exact HwfAout.
Qed.

(** Multi-step preservation, by folding [preservation] over [star]. *)
Corollary preservation_star : forall g e A e',
  wf_ctx g -> typing g e A -> star e e' -> typing g e' A.
Proof.
  intros g e A e' Hwf Hty Hstar.
  apply clos_rt_rt1n_iff in Hstar.
  induction Hstar as [e | e e1 e' H1 Hrest IH]; [exact Hty |].
  apply IH. eapply preservation; eauto.
Qed.
