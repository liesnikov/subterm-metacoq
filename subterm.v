Require Import MetaCoq.Template.All.
Require Import List String Relation_Operators.
Import ListNotations MonadNotation.

(* Require Import sigma. *)

Definition filteri {A: Type} (f : nat -> A -> bool) (l:list A) : list A :=
  let go := fix go n l := match l with
                         | nil => nil
                         | x :: l => if f n x then x::(go (S n) l) else go (S n) l
                         end
  in go 0 l.

Definition ind_eqb (i0 : inductive) (i1 : inductive) : bool :=
  andb (String.eqb i0.(inductive_mind) i1.(inductive_mind))
       (Nat.eqb    i0.(inductive_ind)  i1.(inductive_ind)).

Definition opt_nil {A : Type} (x : option A) : list A := match x with Some a => [a]| None => [] end.

Definition clift0 (n : nat) (t : context_decl) : context_decl :=
  {| decl_name := t.(decl_name);
     decl_body := match t.(decl_body) with
                   | Some q => Some (lift0 n q)
                   | None => None
                  end;
     decl_type := lift0 n t.(decl_type)
  |}.

Definition subterms_for_constructor
           (global_e : global_env)
           (refi : inductive)
           (ref   : term) (* we need the term for exactly this inductive just for the substition *)
           (ntypes : nat) (* number of types in the mutual inductive *)
           (npars : nat) (* number of parameters in the type *)
           (nind : nat) (* number of proper indeces in the type *)
           (ct    : term) (* type of the constructor *)
           (ncons : nat) (* index of the constructor in the inductive *)
           (nargs : nat) (* number of arguments in this constructor *)
                  : list (nat * term * nat)
  := let nct := subst1 ref (1 + ntypes - inductive_ind refi) ct in
     let '(ctx, ap) := decompose_prod_assum [] nct in
     (* now ctx is a reversed list of assumptions and definitions *)
     let len := List.length ctx in
     let params := List.skipn (len - npars) (ctx) in
     let inds := List.skipn npars (snd (decompose_app ap)) in
     let d :=(List.flat_map opt_nil ∘
                    (* so this i represents distance from return object to `t` *)
               mapi (fun i t =>
                       let '(ctx, ar) := decompose_prod_assum [] (decl_type t)
                       in match (fst (decompose_app ar)) with
                          | tInd indj _ => if ind_eqb indj refi
                                          then Some (i, ctx,
                                                     snd (decompose_app ar))
                                          else None
                          | _ => None
                          end)) ctx in
     let construct_cons :=
         fun (* index of a subterm in this constructor *)
           (i: nat)
           (* these are arguments for the function
              that is a parameter of the constructor
              and if applied fully returns something of the needed type *)
           (ctx': context)
           (* these are arguments of the type of the subterm *)
           (args' : list term) =>
           let len' := List.length ctx' in
           let ctxl' := (map (clift0 (2 + i)) ctx') in
           it_mkProd_or_LetIn
             (ctxl' ++ ctx)
             (tApp (tRel (len + len'))
                   ((map (lift0 (len' + len - npars))
                         (to_extended_list params)) ++
                    (map (lift (1 + i + len') len') (List.skipn npars args')) ++
                    (map (lift0 len') inds) ++
                    [tApp (tRel (i + len'))
                          (to_extended_list ctxl');
                     tApp (tConstruct refi ncons [])
                          (map (lift0 len')
                               (to_extended_list ctx))])) in
     mapi (fun i '(n, c, a) => (i, construct_cons n c a, len + List.length c)) d.

Definition subterm_for_ind
           (global_e : global_env)
           (refi : inductive)
           (ref   : term)
           (ntypes : nat) (* number of types in the mutual inductive *)
           (npars : nat)
           (pars  : context)
           (ind   : one_inductive_body)
                  : one_inductive_body
  := let (pai, sort) := decompose_prod_assum global_e ind.(ind_type) in
     let sort := (tSort (Universe.make'' (Level.lProp, false) [])) in
     let inds := List.firstn (List.length pai - npars) pai in
     let leni := List.length inds in
     let aptype1 :=
         tApp ref ((map (lift0 (2 * leni)) (to_extended_list pars)) ++
                   (map (lift0 leni) (to_extended_list inds))) in
     let aptype2 :=
         tApp ref ((map (lift0 (1 + 2 * leni)) (to_extended_list pars)) ++
                   (map (lift0 1) (to_extended_list inds))) in
     let renamer name i := (name ++ "_subterm" ++ (string_of_nat i))%string in
     {| ind_name := (ind.(ind_name) ++ "_direct_subterm")%string;
        (* type_for_direct_subterm npars *)
        ind_type  := it_mkProd_or_LetIn
                       pars
                       (it_mkProd_or_LetIn
                          (inds ++ inds)
                          (tProd nAnon aptype1
                                 (tProd nAnon aptype2 sort)));
        ind_kelim := [InProp];
        ind_ctors :=List.concat
                      (mapi (fun n '(id, ct, k) => (
                        map (fun '(si, st, sk) => (renamer id si, st, sk))
                        (subterms_for_constructor global_e refi ref ntypes npars leni ct n k)))
                        ind.(ind_ctors));
        ind_projs := [] |}.

Definition direct_subterm_for_mutual_ind
            (ge : global_env)
            (mind : mutual_inductive_body)
            (ind0 : inductive) (* internal metacoq representation of inductive, part of tInd *)
            (ref  : term) (* reference term for the inductive type, like (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []) *)
                  : mutual_inductive_body
  := let i0 := inductive_ind ind0 in
     let ntypes := length (ind_bodies mind) in
     {| ind_finite := BasicAst.Finite;
        ind_npars := 0;
        ind_universes := Monomorphic_ctx (LevelSetProp.of_list [], ConstraintSet.empty);
        ind_params := [];
        ind_bodies := (map (subterm_for_ind global_e ind0 ref ntypes
                                           mind.(ind_npars) mind.(ind_params)) ∘
                      (filteri (fun (i : nat) (ind : one_inductive_body) =>
                                  if Nat.eqb i i0 then true else false)))
                      mind.(ind_bodies);
     |}.

Polymorphic Definition subterm (tm : Ast.term)
  : TemplateMonad unit
  :=
    ge_t <- tmQuoteRec tm;;
    let global_e := fst ge_t in
    let tterm := ge_t in
    match tterm with
     | tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0);;
       let direct_subterm := direct_subterm_for_mutual_ind global_e decl ind0 tm in
       v <- tmEval lazy direct_subterm;;
       tmPrint v;;
       tmMkInductive' direct_subterm
     | _ =>
       tmPrint tm;;
       tmFail "is not an inductive"
     end.
