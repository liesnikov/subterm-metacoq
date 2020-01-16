Require Import Local.subterm.

Require Import Equations.Equations.
Require Import MetaCoq.Template.All.
Require Import String.
Import MonadNotation.

Inductive finn (A : Type) : nat -> Set :=
  F1n : forall n : nat, finn A (S n)
| FSn : forall n : nat, finn A n -> finn A (S n).

Inductive fin : nat -> Type :=
  F1 : forall n : nat, fin (let x := S n in x)
| FS : forall n : nat, fin n -> fin (S n).

Definition printer (tm : Ast.term)
  : TemplateMonad unit
  := match tm with
     | tInd ind0 _ =>
       d <- tmQuoteInductive (inductive_mind ind0);;
       tmPrint d
     | _ => tmFail "sorry"
     end.
Run TemplateProgram (printer <%list%>).

Run TemplateProgram (subterm <%list%>).

(* Derive Subterm for list. *)
Run TemplateProgram (printer <%list_direct_subterm%>).

Print list_direct_subterm.

Inductive even : nat -> Prop :=
| even_O : even 0
| even_S : forall n, even n -> even (S n)
with  dummy : nat -> Prop :=
| dummyc : forall n, dummy n
with odd : nat -> Prop :=
| odd_S : forall n, even n -> odd (S n).

Run TemplateProgram (printer <%even%>).

Run TemplateProgram (subterm <%odd%>).
Print odd_direct_subterm.

Definition scope := nat.
Inductive scope_le : scope -> scope -> Set :=
| scope_le_n : forall {n m}, n = m -> scope_le n m
| scope_le_S : forall {n m}, scope_le n m -> scope_le n (S m)
| scope_le_map : forall {n m}, scope_le n m -> scope_le (S n) (S m)
.

Run TemplateProgram (subterm <%scope_le%>).

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
