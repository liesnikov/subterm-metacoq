Require Import Local.subterm.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.
Require Import String.

Require Import List.
Import ListNotations.

Ltac inj H := (injection H; clear H; intro H).

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

Lemma decompose_it_mkProd l m:
  forall c s, (forall n, (c ++ n, s) = decompose_prod_assum n m) ->
  decompose_prod_assum [] (it_mkProd_or_LetIn l m) = (c ++ l, s).
Proof.
  induction l in m |- *; intros c s e; cbn.
  - specialize e with []. rewrite app_nil_r in e. now rewrite app_nil_r.
  - cbn. change ((fold_left (fun acc d => mkProd_or_LetIn d acc) l (mkProd_or_LetIn a m))) with (it_mkProd_or_LetIn l (mkProd_or_LetIn a m)).
    assert (c ++ a :: l = (c ++ [a]) ++ l) as cal. (induction c in |- *; auto; rewrite <- app_comm_cons; rewrite IHc; now rewrite app_comm_cons).
    rewrite cal. apply (IHl (mkProd_or_LetIn a m)).
    unfold mkProd_or_LetIn.
    destruct (decl_body a) eqn: bae; cbn;
    intros n; rewrite <- (app_assoc c [a] n); unfold snoc.
    + assert (vdef (decl_name a) t (decl_type a) = a) as vae.
      (destruct a eqn: eqa; unfold vdef; rewrite <- bae; now reflexivity).
      rewrite vae. exact (e ([a] ++ n)).
    + assert (vass (decl_name a) (decl_type a) = a) as vae.
      (destruct a eqn: eqa; unfold vass; rewrite <- bae; now reflexivity).
      rewrite vae. exact (e ([a] ++ n)).
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
                  0 _ onInductives _ o ind_body).
      2: constructor. eapply (Build_on_ind_body _ _ _ _ _ _ _ _).
      * cbn. unfold subterm_for_ind.
        rewrite ind_arity_eq.
        destruct decompose_prod_assum eqn: decomp_eq.
        pose (surjective_pairing (c,t)) as decomp_eq_h.
        unfold ind_type.
        repeat (rewrite it_mkProd_assoc).
        rewrite <- decomp_eq in decomp_eq_h at 2 3. inversion decomp_eq_h.
        reflexivity.
      * unfold subterm_for_ind.
        rewrite ind_arity_eq.
        destruct decompose_prod_assum eqn: decomp_eq.

        rewrite it_mkProd_assoc. exists (Universe.make' (Level.lProp, false)).
        rewrite it_mkProd_assoc in decomp_eq.
        erewrite decompose_it_mkProd in decomp_eq.

        Focus 2. intro. (* ?c *) Existential 13 := []. reflexivity.
        rewrite app_nil_l in decomp_eq.
        inversion decomp_eq.
        rewrite app_length, PeanoNat.Nat.add_sub, firstn_app, PeanoNat.Nat.sub_diag, firstn_all, app_nil_r. cbn. admit.
      * admit.
      * intros. unfold subterm_for_ind in H. unfold ind_projs in H. destruct (decompose_prod_assum [] (ind_type o)). now contradiction H.
      * cbn. intros x H. unfold subterm_for_ind in H. unfold ind_kelim in H.
        destruct (decompose_prod_assum [] (ind_type o)).
        induction H. rewrite <- H. now cbn. inversion H.
      Unshelve.
    + cbn. constructor.
Abort.


