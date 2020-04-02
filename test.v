Require Import Local.subterm.

Require Import Equations.Equations.
Require Import MetaCoq.Template.All.
Require Import String List.
Import ListNotations.
Import MonadNotation.



Definition printer (tm : Ast.term)
  : TemplateMonad unit
  :=  match tm with
     | tInd ind0 _ =>
       d <- tmQuoteInductive (inductive_mind ind0);;
       tmPrint d
     | _ => tmFail "sorry"
     end.

Section Test.
  Variable p : Type.
  Variable pc : p.
  Inductive test : p -> Type:= .
End Test.

MetaCoq Run (printer <%test%>).



MetaCoq Run (printer <%list%>).
MetaCoq Run (subterm <%list%>).
(*Derive Subterm for list.*)
Compute (<%list_direct_subterm%>).
MetaCoq Run (printer <%list_direct_subterm%>).
Print list_direct_subterm.

Inductive even : nat -> Prop :=
| even_O : even 0
| even_S : forall n, even n -> even (S n)
with  dummy : nat -> Prop :=
| dummyc : forall n, dummy n
with odd : nat -> Prop :=
| odd_S : forall n, even n -> odd (S n).



MetaCoq Run (printer <%even%>).

MetaCoq Run (subterm <%odd%>).
Print odd_direct_subterm.


Inductive finn A : list(A) -> nat -> Type :=
  F1n : forall (l : list A) (n : nat), finn A l (S n)
| FSn : let p := list A in forall (l : p) (n : nat), finn A l n -> finn A l (S n).

Inductive fin A (p : (finn A [] 0)): nat -> Type :=
  F1 : forall n : nat, fin A p (let x := S n in x)
| FS : forall n : nat, fin A p n -> fin A p (S n).

MetaCoq Run (printer <%finn%>).
MetaCoq Run (subterm <%finn%>).
(*Derive Subterm for finn.*)
MetaCoq Run (printer <%finn_direct_subterm%>).
Print finn_direct_subterm.


MetaCoq Run (p <- tmQuote fin;; tmPrint p ).

Definition scope := nat.
Inductive scope_le : scope -> scope -> Set :=
| scope_le_n : forall {n m}, n = m -> scope_le n m
| scope_le_S : forall {n m}, scope_le n m -> scope_le n (S m)
| scope_le_map : forall {n m}, scope_le n m -> scope_le (S n) (S m)
.

MetaCoq Run (subterm <%scope_le%>).

Print scope_le_direct_subterm.
(*
Inductive
scope_le_direct_subterm
    : forall H H0 H1 H2 : scope, scope_le H H0 -> scope_le H1 H2 -> Set :=
    scope_le_S_subterm0 : forall (n m : scope) (H : scope_le n m),
                          scope_le_direct_subterm n m n (S m) H (scope_le_S H)
  | scope_le_map_subterm0 : forall (n m : scope) (H : scope_le n m),
                            scope_le_direct_subterm n m 
                              (S n) (S m) H (scope_le_map H)
*)
