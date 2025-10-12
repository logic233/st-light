From Coq Require Import FSets.FMapPositive.
From Coq Require Import Setoid.
From Coq Require Import List.
Import List.ListNotations.



Section Forall_re.
Variable A E: Type.
Variable (P : E -> A -> E -> Prop).
Inductive Forall_re   : E -> list A -> E -> Prop :=
  | Forall_re_nil : forall (e:E), Forall_re e [] e
  | Forall_re_cons : forall (x : A) (l : list A)(e e1 e2 : E),
                  P e x e1 -> Forall_re e1 l e2 -> Forall_re e (x :: l) e2 .
End Forall_re.

Check Forall.
Theorem Forall_map : forall (A B: Type) (P: B -> Prop) (f: A -> B) (l: list A),
  Forall (fun x => P (f x)) l -> Forall P (map f l).
  Proof.
  intros A B P f l H.
  induction H.
  - (* Case: Forall_nil *)
    simpl. constructor.
  - (* Case: Forall_cons *)
    simpl. constructor.
    + apply H.
    + apply IHForall.
Qed.