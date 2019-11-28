Require Import MetaCoq.Template.All.
Require Import List String.
Require Import Coq.Program.Equality.
Import ListNotations MonadNotation.

Definition filteri {A: Type} (f : nat -> A -> bool) (l:list A) : list A :=
  let go := fix go n l := match l with
                         | nil => nil
                         | x :: l => if f n x then x::(go (S n) l) else go (S n) l
                         end
  in go 0 l.

Definition ind_eq (i0 : inductive) (i1 : inductive) : bool :=
  andb (String.eqb i0.(inductive_mind) i1.(inductive_mind))
       (Nat.eqb i0.(inductive_ind) i1.(inductive_ind)).

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
  (refi : inductive) (ref : term) (npars : nat) (ct : term) (ncons : nat) (nargs: nat)
  : list (nat * term * nat)
  := let nct := subst10 ref ct in
     let '(ctx, ap) := decompose_prod_assum [] nct in
     let len := List.length ctx in
     let params := List.skipn (len - npars) (ctx) in
     (* now ctx is reversed list of assumptions and definitions *)
     let d :=(List.flat_map opt_nil ∘
                  (* so this i represents distance from the innermost object *)
               mapi (fun i t =>
                       let '(ctx, ar) := decompose_prod_assum [] (decl_type t)
                       in match (fst (decompose_app ar)) with
                          | tInd indj _ => if ind_eq indj refi
                                          then Some (i, ctx,
                                                     snd (decompose_app ar))
                                          else None
                          | _ => None
                          end)) ctx in
     let construct_cons := fun (i: nat)
                             (ctx': context)
                             (args' : list term) =>
                             let len' := List.length ctx' in
                             let lctx' := (map (clift0 (2 + i)) ctx') in
                             it_mkProd_or_LetIn
                                   (lctx' ++ ctx)
                                   (tApp (tRel (len + len'))
                                         (map (lift0 (len' + len - (List.length params)))
                                              (to_extended_list params) ++
                                         [tApp (tRel (i + len'))
                                               (to_extended_list lctx');
                                          tApp (tConstruct refi ncons [])
                                               (map (lift0 len')
                                                    (to_extended_list ctx))])) in
     mapi (fun i '(n, c, a) => (i, construct_cons n c a, nargs)) d.

Definition subterm_for_ind
(refi : inductive) (* reference term for the inductive type *)
(ref : term)
(npars : nat)
(pars : context)
(ind : one_inductive_body)
  : one_inductive_body
  := let aptype1 := tApp ref (to_extended_list pars) in
     let aptype2 := tApp ref (map (lift0 1) (to_extended_list pars)) in
     let sort := snd (decompose_prod_assum [] ind.(ind_type)) in
     let renamer := fun name i => (name ++ "_subterm_" ++ (string_of_nat i))%string in
     {| ind_name := (ind.(ind_name) ++ "_direct_subterm")%string;
        (* type_for_direct_subterm npars *)
        ind_type  := it_mkProd_or_LetIn
                       pars
                       (tProd nAnon aptype1 (tProd nAnon aptype2 sort));
        ind_kelim := [InProp];
        ind_ctors :=List.concat
                      (mapi (fun n '(id, ct, k) => (
                        map (fun '(si, st, sk) => (renamer id si, st, sk))
                        (subterms_for_constructor refi ref npars ct n k)))
                        ind.(ind_ctors));
        ind_projs := [] |}.

Definition subterm_for_mutual_ind
            (mind : mutual_inductive_body)
            (ind0 : inductive) (* internal metacoq representation of inductive, part of tInd *)
            (ref  : term) (* reference term for the inductive type, like (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []) *)
                  : mutual_inductive_body
  := let i0 := inductive_ind ind0 in
     {| ind_finite := BasicAst.Finite;
        ind_npars := mind.(ind_npars);
        ind_universes := mind.(ind_universes);
        ind_params := mind.(ind_params);
        ind_bodies := (map (subterm_for_ind ind0 ref mind.(ind_npars) mind.(ind_params)) ∘
                      (filteri (fun (i : nat) (ind : one_inductive_body) =>
                                  if Nat.eqb i i0 then true else false)))
                      mind.(ind_bodies);
        |}.

Inductive nnat (A : Type) : Type :=
  n_zero : nnat A
| n_one : (nat -> nnat (list A)) -> nnat A.

Polymorphic Definition subterm (tm : Ast.term)
  : TemplateMonad unit
  := match tm with
     | tInd ind0 _ =>
       ge_ <- tmQuoteRec tm;;
       decl <- tmQuoteInductive (inductive_mind ind0);;
       let subt := subterm_for_mutual_ind decl ind0 tm in
       v <- tmEval cbv subt;;
       tmPrint v;;
     (* tmPrint (print_term (fst ge_, decl.(ind_universes)) [] true v) *)
       tmMkInductive' v
     | _ => tmPrint tm;; tmFail "is not an inductive"
     end.

Run TemplateProgram (subterm <%list%>).
Print list_direct_subterm.
