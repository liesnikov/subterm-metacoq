Require Import Local.subterm.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.
Require Import String.

Require Import List.
Import ListNotations.

Ltac inj H := (injection H; clear H; intros H).

Lemma ind_inversion:
  forall Sigma mind_body ind,
  wf (Sigma) ->
  declared_minductive (Sigma) (inductive_mind ind) mind_body ->
  let u := universes_decl_of_decl
            (InductiveDecl (inductive_mind ind) mind_body)
  in
  on_inductive (lift_typing typing)
               (Sigma, u)
               (inductive_mind ind) mind_body.
Proof.
  intros Sigma mind_body ind W D u.
  induction W.
  - inversion D.
  - destruct (ident_eq (inductive_mind ind) (global_decl_ident d)) eqn: e;
    unfold declared_minductive in D; cbn in D; rewrite e in D.
    + inj D. subst.
      change (on_global_decl (lift_typing typing) (Σ,, InductiveDecl (inductive_mind ind) mind_body, u) (InductiveDecl (inductive_mind ind) mind_body)).
      apply (WeakeningEnv.weakening_on_global_decl (lift_typing typing) Σ _ _ (InductiveDecl (inductive_mind ind) mind_body)).
      exact WeakeningEnv.weaken_env_prop_typing.
      constructor; assumption. exists [InductiveDecl (inductive_mind ind) mind_body]. reflexivity. assumption.
    + unfold declared_minductive in IHW. apply IHW in D.
      change (on_global_decl (lift_typing typing) (Σ,, d, u) (InductiveDecl (inductive_mind ind) mind_body)).
      apply (WeakeningEnv.weakening_on_global_decl (lift_typing typing) Σ _ _ (InductiveDecl (inductive_mind ind) mind_body)).
      exact WeakeningEnv.weaken_env_prop_typing.
      constructor; assumption. exists [d]. reflexivity. assumption.
Qed.


Lemma Alli_nth_error {A : Type} P m (l : list A):
        Alli P m l ->
        forall n o, nth_error l n = Some o ->
               P (m + n) o.
Proof.
  induction 1; intros k o m.
  - rewrite (nth_error_nil k) in m. congruence.
  - induction k; cbn in m.
    + inversion m. subst. rewrite (Coq.Arith.Plus.plus_comm). now assumption.
    + apply IHX in m. rewrite (Coq.Arith.Plus.plus_comm). cbn.
      cbn in m. rewrite (Coq.Arith.Plus.plus_comm) in m. assumption.
Qed.

Lemma it_mkProd_assoc a b c:
  it_mkProd_or_LetIn b (it_mkProd_or_LetIn a c) = it_mkProd_or_LetIn (a ++ b) c.
Proof. induction a in b, c |- *; cbn; auto. Qed.

Goal forall Sigma mind_body ref ind,
    wf Sigma ->
    {u & ref = tInd ind u} ->
    declared_minductive (Sigma) (inductive_mind ind) mind_body ->
    forall v, direct_subterm_for_mutual_ind mind_body ind ref = Some v ->
    wf (Sigma ,, InductiveDecl ("random"%string) v).
Proof.
  intros Sigma mind_body ref ind WF EU DM v Sv.
  pose (Monomorphic_ctx (LevelSet.empty, ConstraintSet.empty)) as ctx.
  constructor.
  - inversion WF; constructor; try assumption.
  - admit.
  - admit.
  - constructor; unfold direct_subterm_for_mutual_ind in Sv;
    destruct (nth_error (ind_bodies mind_body) (inductive_ind ind)) eqn: ind_body; cbn in Sv.
    2:congruence. inj Sv.
    + destruct (ind_inversion Sigma mind_body ind WF DM).
      rewrite <- Sv; constructor.
      pose (universes_decl_of_decl
             (InductiveDecl (inductive_mind ind) mind_body)) as u.
      destruct (Alli_nth_error
                  (on_ind_body (lift_typing typing)
                               (Sigma, u)
                               (inductive_mind ind) mind_body)
                  0 _ onInductives _ o ind_body) eqn: X_eq.
      2: constructor. econstructor.
      * unfold subterm_for_ind.
        rewrite ind_arity_eq.
        destruct decompose_prod_assum eqn: decomp_eq.
        pose (surjective_pairing (c,t)) as decomp_eq_h.
        rewrite it_mkProd_assoc. rewrite it_mkProd_assoc.
        rewrite <- decomp_eq in decomp_eq_h at 2 3. inversion decomp_eq_h.
        reflexivity.
      * unfold subterm_for_ind.
        rewrite ind_arity_eq.
        destruct decompose_prod_assum eqn: decomp_eq.
        cbn.

    + cbn. constructor.
Abort.
