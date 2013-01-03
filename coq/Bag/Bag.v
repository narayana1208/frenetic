Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Common.Types.
Require Import Omega.

Local Open Scope list_scope.
Local Open Scope signature_scope.
Local Open Scope equiv_scope.

Create HintDb bag.

(* TODO(arjun): I'm not paying attention to levels and associativity. Fix. *)
Reserved Notation "{| x |}" (at level 70, no associativity).
Reserved Notation "{| |}" (at level 70, no associativity).
Reserved Notation "x <+> y" (at level 69, right associativity).

Module Bag.

  Inductive bag (A : Type) := 
  | Empty : bag A
  | Singleton : A -> bag A
  | Union : bag A -> bag A -> bag A
  | FromList : list A -> bag A.

  Implicit Arguments Empty [[A]].
  Implicit Arguments Singleton [[A]].
  Implicit Arguments Union [[A]].
  Implicit Arguments FromList [[A]].

  Definition t := bag.

  Section Methods.

    Variable A : Type.
    Variable E : Eq A.
    
    Fixpoint multiplicity (x : A) (bag : bag A) := 
      match bag with
        | Empty => 0
        | Singleton y => 
          match eqdec x y with
            | left _ => 1
            | right _ => 0
          end
        | Union bag1 bag2 => multiplicity x bag1 + multiplicity x bag2
        | FromList lst =>
          List.fold_right 
          (fun y sum =>
            match eqdec x y with
              | left _ => S sum
              | right _ => sum
            end) 0 lst
      end.
    
    Fixpoint to_list (bag : bag A) :=
      match bag with
        | Empty => nil
        | Singleton x => [x]
        | Union bag1 bag2 => to_list bag1 ++ to_list bag2
        | FromList lst => lst
      end.

    Definition Bag_equiv (x y : bag A) := 
      forall (e : A), multiplicity e x = multiplicity e y.

    Hint Constructors bag.

    Lemma Bag_equiv_is_Equivalence : Equivalence Bag_equiv.
    Proof with auto.
      split.
      unfold Reflexive. unfold Bag_equiv...
      unfold Symmetric. unfold Bag_equiv.
      intros.
      remember (H e)...
      unfold Transitive. unfold Bag_equiv.
      intros.
      remember (H e).
      remember (H0 e).
      rewrite -> e0...
    Qed.

    Instance Bag_Equivalence : Equivalence Bag_equiv.
    Proof.
      exact Bag_equiv_is_Equivalence.
    Qed.

    Lemma union_iff : forall (x : A) (b1 b2 : bag A),
      multiplicity x (Union b1 b2) = multiplicity x b1 + multiplicity x b2.
    Proof with auto.
      reflexivity.
    Qed.

    Instance union_m : 
      Proper (Bag_equiv ==> Bag_equiv ==> Bag_equiv) Union.
    Proof with auto.
      unfold Proper.
      unfold respectful.
      unfold Bag_equiv.
      intros.
      rewrite union_iff.
      rewrite union_iff...
    Qed.

    Add Morphism Union with signature 
      Bag_equiv ++> Bag_equiv ++> Bag_equiv as union_s_m.
      apply union_m.
    Qed.

    Lemma union_comm : forall x y, Union x y === Union y x.
    Proof with auto.
      unfold Equivalence.equiv.
      unfold Bag_equiv.
      intros.
      simpl.
      omega.
    Qed.

    Lemma union_assoc : forall x y z,  
      Union (Union x y) z === Union x (Union y z).
    Proof with auto.
      unfold Equivalence.equiv.
      unfold Bag_equiv.
      intros.
      simpl.
      omega.
    Qed.
    
    Lemma union_empty_l : forall x, Union Empty x === x.
    Proof with auto.
      unfold Equivalence.equiv.
      unfold Bag_equiv.
      intros.
      simpl.
      reflexivity.
    Qed.

    Lemma union_empty_r : forall x, Union x Empty === x.
    Proof.
      intros.
      rewrite union_comm. apply union_empty_l.
    Qed.

    Definition unions (bags : list (bag A)) : bag A :=
      fold_right Union Empty bags.

    Lemma bag_unions_app : forall (lst lst0 : list (bag A)),
      unions (lst ++ lst0) === Union (unions lst) (unions lst0).
    Proof with auto.
      unfold Equivalence.equiv.
      unfold Bag_equiv.
      intros.
      induction lst...
      simpl.
      simpl in IHlst.
      omega.
    Qed.

    Lemma pop_union_l : forall (b b0 b1: bag A),
      b0 === b1 ->
      Union b b0 === Union b b1.
    Proof.
      intros.
      simpl.
      rewrite -> H.
      apply reflexivity.
    Qed.

   Fixpoint depth (b : bag A) :=
     match b with
       | Singleton _ => 1
       | Empty => 1
       | FromList _ => 1
       | Union l r => max (depth l) (depth r)
     end.

    Lemma rotate_union : forall (b b0 b1 : bag A),
      Union b b0 === b1 ->
      Union b0 b === b1.
    Proof with auto.
      intros.
      rewrite -> union_comm.
      exact H.
    Qed.

    Lemma unions_app : forall (lst lst0 : list (bag A)),
      unions (lst ++ lst0) === Union (unions lst) (unions lst0).
    Proof with auto.
      unfold Equivalence.equiv.
      unfold Bag_equiv.
      intros.
      simpl.
      induction lst...
      simpl in *.
      omega.
    Qed.

    Lemma from_list_cons : forall x xs,
      FromList (x :: xs) === Union (Singleton x) (FromList xs).
    Proof with auto.
      unfold Equivalence.equiv.
      unfold Bag_equiv.
      intros.
      simpl.
      destruct (eqdec e x)...
    Qed.

  End Methods.

  Lemma map_union : forall (A B : Type) {EA : Eq A} {EB : Eq B}
      (f : A -> B) (bag1 bag2 : bag A),
      Bag_equiv EB (FromList (map f (to_list (Union bag1 bag2))))
      (Union (FromList (map f (to_list bag1))) 
        (FromList (map f (to_list bag2)))).
  Proof with auto.
    intros.
  Admitted.

  Lemma unions_unlist : forall (A B : Type) (EA : Eq A) (EB : Eq B)
    (f : A -> bag B) (lst : list A) (bag : bag A),
    Bag_equiv EB
      (unions (map f (to_list (Union (FromList lst) bag))))
      (Union (unions (List.map f lst))
        (unions (List.map f (to_list bag)))).
  Proof with auto.
    unfold Equivalence.equiv.
    unfold Bag_equiv.
    intros.
    induction lst...
    simpl.
    simpl in IHlst.
    rewrite -> IHlst.
    omega.
  Qed.

End Bag.

Notation "x <+> y" := (Bag.Union x y) : bag_scope.
Notation "{| x |}" := (Bag.Singleton x) : bag_scope.
Notation "{| |}" := (Bag.Empty) : bag_scope.

Hint Rewrite 
  Bag.union_empty_r 
  Bag.union_empty_l
  Bag.union_assoc 
  Bag.unions_app
  map_app 
  Bag.from_list_cons : bag.


Instance Bag_Equivalence `(A : Type, E : Eq A): Equivalence (Bag.Bag_equiv E).
Proof.
  exact (Bag.Bag_equiv_is_Equivalence E).
Qed.


Add Parametric Morphism (A : Type) (E : Eq A) : Bag.Union with signature 
  Bag.Bag_equiv E ++> Bag.Bag_equiv E ++> Bag.Bag_equiv E as union_s_m.
  apply Bag.union_m.
Qed.
