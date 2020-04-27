From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst.
From MetaCoq.PCUIC Require TemplateToPCUIC PCUICToTemplate.

From MetaCoq.Template Require Import config monad_utils utils TemplateMonad.
From MetaCoq.Template Require Ast.
Import MonadNotation.
Require Import List String.
Import ListNotations.


Definition ex := (tInd {| inductive_mind := "Coq.Init.Logic.ex"; inductive_ind := 0 |} []).
Definition sigma := (tInd {| inductive_mind := "Coq.Init.Specif.sigT"; inductive_ind := 0 |} []).
Definition acc := (tInd {| inductive_mind := "Coq.Init.Wf.Acc"; inductive_ind := 0 |} []).

Definition sigmaize (u : context_decl) (v : term) :=
  match (decl_body u) with
  | Some body => tLetIn (decl_name u) body (decl_type u) v
  | None => mkApps sigma [(decl_type u) ;
                      tLambda (decl_name u) (decl_type u) (tApp v (tRel 0))]
  end.

Fixpoint sigma_pack_go (n: nat) (c : context) (t : list term -> term) :=
  match c with
  | [] => t
  | ch :: ct =>
    match (decl_body ch) with
    | Some body =>
      sigma_pack_go (n - 1) ct (fun l => tLetIn (decl_name ch) body (decl_type ch) (t l))
    | None =>
      sigma_pack_go (n - 1) ct (fun l =>
      mkApps sigma [(decl_type ch);
               tLambda (decl_name ch) (decl_type ch) (t (tRel n :: l))])
    end
  end.

Definition sigma_pack_arity (t : term) : term
  := let (pai, c) := decompose_prod_assum [] t in
    (sigma_pack_go (List.length pai - 1) pai (fun l => mkApps t l) []).

Definition sigma_pack_inductive
           (i : inductive)
           (m : mutual_inductive_body)
              : option term :=
  (*let params := (ind_params m) in*)
  match (List.nth_error (ind_bodies m) (inductive_ind i)) with
  | None => None
  | Some ind =>
    let (inds, _) := decompose_prod_assum [] (ind_type ind) in
    Some (sigma_pack_go (List.length inds - 1) inds (fun l => mkApps (tInd i []) l) [])
  end.

Definition pack_inductive (t : Ast.term) : TemplateMonad (Ast.term) :=
    match t with
    | Ast.tInd ind0 _ =>
      decl <- tmQuoteInductive (inductive_mind ind0);;
      match (sigma_pack_inductive
               ind0
               (TemplateToPCUIC.trans_minductive_body decl)) with
      | None =>
        tmPrint t;;
        @tmFail (Ast.term) "Coulnd't pack inductive"
      | Some d =>
        v <- tmEval lazy (PCUICToTemplate.trans d);;
        @tmReturn (Ast.term) v
      end
    | _ =>
      tmPrint t;;
      @tmFail (Ast.term) " is not an inductive"
    end.


From MetaCoq.Template Require Import All.

Inductive fin (A : Type) : nat -> Type :=
| fin0 : forall n, fin A n
| finS : forall n, fin A n -> fin A (S n).


MetaCoq Run (pack_inductive <%fin%>).
