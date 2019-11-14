Require Import MetaCoq.Template.All.
Require Import List String.
Require Import Coq.Program.Equality.
Import ListNotations MonadNotation.

Fixpoint filteri_rec {A} (f : nat -> A -> bool) (l : list A) (n : nat) : list A :=
  match l with
  | [] => []
  | hd :: tl => if f n hd then hd :: filteri_rec f tl (S n)
                        else filteri_rec f tl (S n)
  end.

Definition filteri {A} (f : nat -> A -> bool) (l : list A) := filteri_rec f l 0.

Polymorphic Fixpoint type_for_direct_subterm
            (npars : nat)
            (quot_type : Ast.term)
            (typ : Ast.term)
  : Ast.term
  :=
    let
      renamer := fun p => match p with
                  | nAnon => nAnon
                  | nNamed i => nNamed (i ++ "'")%string
                  end
    in
    match npars with
     | 0 => match typ with
           | tProd p ty rst => tProd p
                                    ty
                                    (tProd (renamer p)
                                           ty
                                           (type_for_direct_subterm 0 rst))
           | otherwise => otherwise
           end
     | S n' => match typ with
              | tProd p ty rst => tProd p ty (type_for_direct_subterm n' rst)
              | otherwise => otherwise
              end
    end.

Compute (type_for_direct_subterm 1 (tProd (nNamed "A")
                                (tSort
                                   (Universe.make''
                                      (Level.Level "Coq.Vectors.VectorDef.3",
                                      false) []))
                                (tProd nAnon
                                   (tInd
                                      {|
                                      inductive_mind := "Coq.Init.Datatypes.nat";
                                      inductive_ind := 0 |} [])
                                   (tSort
                                      (Universe.make''
                                         (Level.lSet, false)
                                         [(Level.Level "Coq.Vectors.VectorDef.3",
                                          false)]))))).

Polymorphic Fixpoint subterm_present
            (ref : nat)
            (typ : Ast.term)
  : bool
  := match typ with
     | tRel n => if Nat.eqb n ref then true else false
     | tProd n ty bd => (subterm_present ref ty) || (subterm_present (S ref) bd)
     | tApp f l => (subterm_present ref f) || fold_left (fun b => b || subterm_present ref) l false
     | tCase t1 k t2 => subterm_present ref t1
     | tProj _ t => subterm_present ref t
     | 




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
