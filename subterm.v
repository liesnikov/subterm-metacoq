Require Import MetaCoq.Template.All.
Require Import List String.
Require Import Coq.Program.Equality.
Import ListNotations MonadNotation.


Polymorphic Definition subterm_for_ind
            (npars : nat)
            (ind : one_inductive_body)
  : one_inductive_body
  := {| ind_name := (ind.(ind_name) ++ "_direct_subterm")%string ;
        ind_type  := type_for_direct_subterm npars ind.(ind_type);
        ind_kelim := [InProp] ;
        ind_ctors := map (fun '(id, t, k) =>
                            ((id ++ "_direct_subterm")%string,
                             (tRel 0), k))
                         ind.(ind_ctors);
        ind_projs := [] |}.

Polymorphic Definition subterm_for_mutual_ind
            (mind : mutual_inductive_body)
            (ind0 : inductive)
                  : mutual_inductive_body
  := let i0 := inductive_ind ind0 in
     {| ind_finite := BasicAst.Finite;
        ind_npars := mind.(ind_npars);
        ind_universes := mind.(ind_universes) ;
        ind_params := mind(.ind_params);
        ind_bodies := ((map (subterm_for_ind mind.(ind_npars)) ∘
                      (filteri (fun (i : nat) (ind : one_inductive_body) =>
                                  if Nat.eqb i i0 then true else false)))
                      mind.(ind_bodies);
        |}.


Polymorphic Definition subterm (tm : Ast.term)
  : TemplateMonad unit
  := match tm with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       let subt := subterm_for_mutual_ind decl ind0 in
       tmMkInductive' subt
     | _ => tmPrint tm;; tmFail "is not an inductive"
     end.

Run TemplateProgram (subterm <%list%>).

Print nat_direct_subterm.
