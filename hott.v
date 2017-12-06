

Lemma hott_eq_refl : forall A:Type, forall x:A, x=x.
Proof.
  intros.
  exact (eq_refl x).
Qed.



(*
Ideas:

Indution type vs traditionnal representation:
   - boolean: forall A:Type,  A -> A -> A
https://en.wikipedia.org/wiki/Calculus_of_constructions


*)

(*

Induction Type:


T1, ..., Tn : Type
fi : Ti
ki indices

-------
A:Type
c1 : T1 x A^k1 -> A
...
cn : Tn x A^kn -> A

ind_elim:
forall P: A -> Type,
    (  forall t1:T1,  a1:A, ..., ak1:A, P(a1) -> ... -> P(ak1) -> P( c1(t1, a1, ..., ak1) ) )
->  (  forall t2:T2,  a1:A, ..., ak2:A, P(a1) -> ... -> P(ak2) -> P( c2(t2, a1, ..., ak2) ) )
-> ...
-> forall a:A, P(A)

extension: ind_elim P f1 ... fn (c1 t1 a1 ... ak1) = f1 t1 (ind_elim P f1 ... f2 a1) ... (ind_elim P f1 ... f2 ak1)
etc

Arg: why equality here !

Can we keep only two constructor:
T1 : Type
T2 : Type -> Type
------------------
c1 : T1 -> A
c2 : T2 A -> A




Quotient type:

A : Type
f: A -> A -> Type
----------
Quot(A,f) : Type
cons: A -> Quot(A,f)

forall P:Quot(A,f) -> Type, P

-> forall q : Quot(A,f): P(q)

or

A:Type
f:A->B
----------
Quot(A,B,f) : Type

cons : A -> Quot A B f
dest : Quot A B f -> B

ext  : forall T : Type,
         (B -> T) -> Quot(A,B,f) -> T

ext2 : forall T:  Type,
       forall P : B -> T,
       (forall b:B, P b) -> (forall q : Quot(A,B,f), ext T P q)


rev  : forall a : A,
         dest const a = f a

quot_elim : ext T P (cons a) = P (f a)

quot_elim2 : ext2 T P h (cons a) = h (f a)


Goddammit these equalities again !
Can we cheat like that ?

rev  : forall a : A, forall P:B -> Type, P dest const a -> P f a

I already hate myself for writing that....


*)



Lemma hott_eq_ind : forall A:Type, forall P:A ->Type, forall x:A, P x -> forall y:A, y=x -> P y.
Proof.
  intros.
  rewrite H.
  exact X.
Qed.


Print hott_eq_ind.

Lemma hott_eq_ind_2 : forall A:Type, forall P:A ->Type, forall x:A, forall p:P x, hott_eq_ind A P x p x eq_refl = p.
Proof.
  intros.
  unfold hott_eq_ind.
Qed.


Print hott_eq_ind.



Lemma hott_eq_sym : forall A:Type, forall x y:A, (x = y) -> (y = x).
Proof.
  intros.
  rewrite H.
  exact (eq_refl y).
Qed.

Print hott_eq_sym.


Lemma hott_eq_refl_inv_is_inv:
  forall A:Type, forall x:A, hott_eq_sym A x x (eq_refl x) = (eq_refl x).
Proof.
  intros.
  unfold hott_eq_sym.
  





Definition A:Set.
Proof.
  exact nat.
Qed.



Definition a:nat.
Proof.
exact 1.
Qed.

Print eq_rec.
Extraction eq_rec.


(*
Inductive teq : forall (A:Type), A -> A -> Type := eq_refl : forall (A:Type) (x:A), teq A x x.

Print teq_rect.
*)


Definition teq : forall (A:Type), A -> A -> Type.
Admitted.

Definition teq_refl : forall (A:Type) (x:A), teq A x x.
Admitted.

Definition teq_rect :
  forall (A:Type),
  forall (x:A) (P:A -> Type),
    (P x) -> forall (y:A), (teq A x y) -> (P y).
Admitted.











