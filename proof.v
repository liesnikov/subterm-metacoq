Require Import Local.subterm.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Checker.All.
Require Import String.
Require Import Arith.Wf_nat.

Require Import List.
Import ListNotations.

Ltac inj H := (injection H; clear H; intro H).

Lemma decompose_it_mkProd l m c s:
  (forall n, (c ++ n, s) = decompose_prod_assum n m) ->
  decompose_prod_assum [] (it_mkProd_or_LetIn l m) = (c ++ l, s).
Proof.
  generalize c s. clear c s.
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

Lemma rev_list_ind_t {A} : forall P:list A-> Type,
  P [] ->
  (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
  forall l:list A, P (rev l).
Proof.
  induction l; auto.
Qed.

Theorem rev_ind_t {A} : forall P:list A -> Type,
  P [] ->
  (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
Proof.
  intros.
  generalize (rev_involutive l).
  intros E; rewrite <- E.
  apply (rev_list_ind_t P).
  - auto.
  - simpl. intros. apply (X0 a (rev l0)). auto.
Qed.

Lemma type_type {Sigma} {Gamma} {u} {t} {T}:
  (Sigma, u);;; Gamma |- t : T ->
  {s & (Sigma, u);;; Gamma |- T : tSort s}.
Proof.
  intros.
  induction X.
  - assert (n < #|Γ|) as lenG. (now apply nth_error_Some).
    pose (nth_error_All_local_env lenG a).
    admit.
  - induction l; cbn.
    
Admitted.


Lemma it_mkProd_typed {Sigma} {Gamma} {u} {l} {r} {s}:
  (Sigma, u);;; (l ++ Gamma) |- r : tSort s ->
  {s & (Sigma, u);;; Gamma |- it_mkProd_or_LetIn l r : tSort s}.
Proof.
  revert r s.
  induction l; intros.
  - eauto using app_nil_r, X.
  - simpl.
    assert ({s1 & (Sigma, u);;; (l ++ Gamma) |- mkProd_or_LetIn a r : tSort s1}).
    destruct a eqn: eqa.
    destruct decl_body.
    assert (0 < #|(a :: l) ++ Gamma|) as lenG; simpl; try micromega.Lia.lia.
    subst. pose (nth_error_All_local_env lenG (typing_wf_local X)) as o.
    cbn in o. try destruct o as [eo o].
    unfold mkProd_or_LetIn. simpl.
    destruct (type_type o). eexists.
    apply (type_Conv _ _ _ (tLetIn decl_name t decl_type (tSort s)) _).
    eapply type_LetIn. exact t0. exact o. unfold vdef, snoc. exact X.
    unfold isWfArity. right. eexists. apply type_Sort.
    exact (typing_wf_local o).
    inversion o.
    + admit.
Admitted.

Goal forall Sigma mind_body ref ind u,
    wf_ext Sigma ->
    ref = tInd ind u ->
(*    consistent_instance_ext Sigma mind_body.(ind_universes) u ->*)
    declared_minductive (Sigma) (inductive_mind ind) mind_body ->
    forall v, direct_subterm_for_mutual_ind mind_body ind ref = Some v ->
    wf (Sigma.1 ,, ("random"%string, InductiveDecl  v)).
Proof.
  intros Sigma mind_body ref ind ui WF EtInd (*CUI*) DM v Sv.
  destruct WF as [WF WFU].
  constructor.
  - inversion WF; constructor; try assumption.
  - admit.
  - unfold direct_subterm_for_mutual_ind in Sv.
    destruct (nth_error (ind_bodies mind_body) (inductive_ind ind)) eqn: ind_body; cbn in Sv.
    inj Sv. 2 : congruence.
    destruct (WeakeningEnv.on_declared_minductive WF DM).
    rewrite <- Sv. cbn. admit.
  - unfold direct_subterm_for_mutual_ind in Sv.
    destruct (nth_error (ind_bodies mind_body) (inductive_ind ind)) eqn: ind_body; cbn in Sv.
    inj Sv. 2 : congruence.
    constructor;
    destruct (WeakeningEnv.on_declared_minductive WF DM).
    + rewrite <- Sv; constructor.
      pose (ind_universes mind_body) as u.
      destruct (Alli_nth_error
                  (on_ind_body (lift_typing typing)
                               (Sigma.1, u)
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

        rewrite it_mkProd_assoc. cbn.
        eexists.
        (*exists (Universe.make' (Level.lProp, false)).*)
        rewrite it_mkProd_assoc in decomp_eq.
        erewrite decompose_it_mkProd in decomp_eq.

        Focus 2. intro. (* ?c *) Existential 11 := []. reflexivity.

        rewrite app_nil_l in decomp_eq.
        inversion decomp_eq.
        rewrite app_length, PeanoNat.Nat.add_sub, firstn_app,
                PeanoNat.Nat.sub_diag, firstn_all, app_nil_r, <- it_mkProd_assoc.
        cbn in onParams. cbn. admit.
      * unfold on_udecl_decl. cbn.
        rewrite Sv.

        unfold ind_ctors.
        unfold subterm_for_ind at 2.
        destruct decompose_prod_assum eqn: decomp_eq.
        destruct o eqn: eqo. unfold Ast.ind_ctors.
        unfold mapi. generalize 0.
        unfold on_constructors. simpl in onConstructors.
        clear ind_sorts.
        induction onConstructors as [ | a b l m onAB onLM IH]; intro n.
        -- (* MetaCoq 8.11 broke this *)
           (*simpl. unfold on_constructors. apply All2_nil.*)
           admit.
        -- unfold mapi. rewrite mapi_rec_eqn.
           destruct a. destruct p.
           rewrite concat_cons.
           set (tail n := (concat (mapi_rec (fun (n1 : nat) '(id', ct, k) => map
             (fun '(si, st, sk) =>
              ((id' ++ "_subterm" ++ string_of_nat si)%string, st, sk))
             (subterms_for_constructor ind ref #|ind_bodies mind_body|
                #|ind_params mind_body|
                #|firstn (#|c| - #|ind_params mind_body|) c| ct n1 k))
                                           l  n))).
           fold (tail (S n)). fold (tail n) in IH.
           unfold subterms_for_constructor at 1.

           destruct (decompose_prod_assum [] t0) as [ca cs] eqn: cteq.
           unfold on_constructor, on_type in onAB.
           inversion onAB as [onAB_type [[cons_args cons_concl_head cons_inds cons_eq] WTlocal]].
           simpl in cshape_eq. rewrite cshape_eq in cteq.
           rewrite it_mkProd_assoc in cteq.
           rewrite (decompose_it_mkProd _ _
                                        []
                                        (mkApps cons_inds (to_extended_list_k (ind_params mind_body) #|cons_args| ++ cons_eq)))
             in cteq.
           Focus 2.
           set (ll := (to_extended_list_k (ind_params mind_body) #|cons_args| ++ cons_eq)).
           destruct ll eqn: ll_eq; simpl; reflexivity.
           inversion cteq.
           admit.
      * intros. unfold subterm_for_ind in H. unfold ind_projs in H.
        destruct (decompose_prod_assum [] (ind_type o)). now contradiction H.
      * cbn. unfold ind_kelim, subterm_for_ind.
        now destruct (decompose_prod_assum [] (ind_type o)); cbn.
    + subst. now constructor.
    + subst. now simpl.
    + (* ind_guard - just assume that it holds?*) admit.
Admitted.
