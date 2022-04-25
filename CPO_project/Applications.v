From Coq Require Import Arith.
Require Import Psatz.
Require Export Setoid Morphisms.
Set Implicit Arguments.

From Project Require Import FiniteSet.
From Project Require Import CPO.

Require Import Bool.

Section TruthValueInstances.

Program Instance Prop_B : B_param :=
  {|
    B := Prop;
    K A := True;
    is_true P := P;
    BTrue := True;
    BFalse := False;
    BAnd := and;
    BOr := or;
    BImpl P Q := P -> Q;
    BForall V Pv := forall v, Pv v;
    BExists V Pv := exists v, Pv v;
  |}.


Program Definition bool_fin : fin bool := {| el := cons true (cons false nil) |}.
Next Obligation. destruct a; destruct b. now left. now right. now right. now left. Qed.
Next Obligation. destruct a. now left. right. now left. Qed.


 Program Instance Bool_B : B_param :=
  {|
    B := bool;
    K := fin;
    is_true := Is_true;
    BTrue := true;
    BFalse := false;
    BAnd := andb;
    BOr := orb;
    BImpl := implb;
    BForall V := fun P => List.forallb P (el (projT2 V));
    BExists V := fun P => List.existsb P (el (projT2 V));
  |}.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. exists (el (@funP A X P)). apply (eq_dec (@funP A X P)).
   apply (all_el (@funP A X P)). Defined.
  Next Obligation. exists (el (@funAB A B X X0)). apply (eq_dec (@funAB A B X X0)).
   apply (all_el (@funAB A B X X0)). Defined.
  Next Obligation. exists (el (@funAbool A X)). apply (eq_dec (@funAbool A X)).
   apply (all_el (@funAbool A X)). Defined.
  Next Obligation.
    split; intro Q. apply Is_true_eq_left. apply List.forallb_forall. 
    intros x Hx. apply Is_true_eq_true. apply Q.
    intro x. apply Is_true_eq_left. apply Is_true_eq_true in Q. rewrite List.forallb_forall in Q.
    apply Q. cbn in *. apply (all_el X).
  Qed.
  Next Obligation.
    split; intro Q. destruct Q as [x Hx]. apply Is_true_eq_left. apply List.existsb_exists.
    exists x. split. cbn in *. apply (all_el X). now apply Is_true_eq_true.
    apply Is_true_eq_true in Q. apply List.existsb_exists in Q. destruct Q as [x Hx]. exists x.
    apply Is_true_eq_left. apply Hx. Qed.

End TruthValueInstances.


Program Definition eqbool {X : Type} {X_fin : fin X} (x y : X) : bool := match (eq_dec X_fin x y) with
  | left _ => true
  | right _ => false
  end.

Lemma eqbool_refl {X : Type} {X_fin : fin X} : 
  forall (x y : X), x = y <-> Is_true (eqbool (X_fin := X_fin) x y).
  Proof. intros. unfold eqbool. now destruct (eq_dec X_fin x y). Qed.

Lemma eqbool_trans {X : Type} {X_fin : fin X} : 
  forall (x y z : X), Is_true (eqbool (X_fin := X_fin) x y) -> 
                      Is_true (eqbool (X_fin := X_fin) y z) -> 
                      Is_true (eqbool (X_fin := X_fin) x z).
 Proof. intros x y z Hxy Hyz. unfold eqbool in *.
  destruct (eq_dec X_fin x y); destruct (eq_dec X_fin y z);
  destruct (eq_dec X_fin x z); try easy.
  contradict n. now rewrite e. Qed.




Section Basic_CPOs.

(* ----- Defining Propositions as a CPO over Prop ----- *)

Program Definition Prop_valid_type := existT (fun P => True) Prop _.

Program Instance B_PO_Prop : @B_PO Prop_B Prop_valid_type :=
  {|
    weq P Q := P <-> Q;
    leq P Q := P -> Q;
  |}.
Next Obligation.
  apply Build_PreOrder.
  + now intros.
  + intros P Q R. tauto.
Qed.

Program Instance B_CPO_Prop : B_CPO B_PO_Prop :=
  {| 
     sup D := exists2 P, D P & P;
  |}.
Next Obligation. firstorder. Qed.

Program Instance B_Lattice_Prop : B_CPO B_PO_Prop :=
  {| 
     sup D := exists2 P, D P & P;
  |}.
Next Obligation. firstorder. Qed.


(* ----- Defining Booleans as a CPO over booleans ----- *)

 Program Definition leqb (b1 b2 : bool) := eqbool (X_fin := bool_fin) b1 false
                                         || eqbool (X_fin := bool_fin) b2 true.

Definition bool_valid_type := existT fin bool bool_fin.

Program Instance B_PO_bool : @B_PO Bool_B bool_valid_type :=
  {|
    weq x y := eqbool (X_fin := bool_fin) x y; (*leqb x y && leqb y x;*)
    leq := leqb;
  |}.
Next Obligation.
  apply Build_PreOrder.
  + intro x. destruct x; unfold leqb; apply orb_prop_intro; [right | left]; now apply eqbool_refl.
  + intros x y z Hxy Hyz. unfold leqb in *. apply orb_prop_intro. apply orb_prop_elim in Hxy, Hyz.
    destruct Hxy. now left. destruct Hyz. apply eqbool_refl in H, H0. rewrite H in H0. now contradict H0.
    now right.
Qed.
Next Obligation. split; intro H. apply eqbool_refl in H. rewrite H.
   split; now apply B_PO_bool_obligation_1.
   destruct x, y; try (now apply eqbool_refl); destruct H as [H1 H2];
   [apply orb_prop_elim in H1 as HF | apply orb_prop_elim in H2 as HF]; destruct HF as [HF | HF]; apply eqbool_refl in HF;
   now contradict HF.
Qed.

Program Instance B_CPO_bool : B_CPO B_PO_bool :=
  {| 
     sup D := D true;
  |}.
  Next Obligation. destruct z.
    split; intros; apply orb_prop_intro; right; now apply eqbool_refl.
    split.
    + intros Hsupz y HDy. destruct y; try (apply orb_prop_intro; left; now apply eqbool_refl).
      destruct (D true). apply orb_prop_elim in Hsupz. destruct Hsupz as [HF | HF];
      apply eqbool_refl in HF; now contradict HF. contradict HDy.
    + intro H. specialize H with true. destruct (D true). now apply H.
      apply orb_prop_intro. left. now apply eqbool_refl.
   Qed.
Program Instance B_Lattice_bool : B_CPO B_PO_bool :=
  {| 
     sup D := D true;
  |}.
  Next Obligation. destruct z.
    split; intros; apply orb_prop_intro; right; now apply eqbool_refl.
    split.
    + intros Hsupz y HDy. destruct y; try (apply orb_prop_intro; left; now apply eqbool_refl).
      destruct (D true). apply orb_prop_elim in Hsupz. destruct Hsupz as [HF | HF];
      apply eqbool_refl in HF; now contradict HF. contradict HDy.
    + intro H. specialize H with true. destruct (D true). now apply H.
      apply orb_prop_intro. left. now apply eqbool_refl.
   Qed.


End Basic_CPOs.




Section CPO_Examples.

Variant CPO_set : Type := bottom : CPO_set | x1 : CPO_set | x2 : CPO_set.

Program Definition CPO_fin : fin (CPO_set) := {| el := cons x2 (cons x1 (cons bottom nil)) |}.
Next Obligation. destruct a; destruct b; try (now left); try (right; intro; inversion H). Defined.
Next Obligation. destruct a; intuition. Defined.

Definition CPO_valid_type := existT fin CPO_set CPO_fin.


 Program Definition leq3 (x y : CPO_set) := eqbool (X_fin := CPO_fin) x y 
                                         || eqbool (X_fin := CPO_fin) x bottom 
                                         || eqbool (X_fin := CPO_fin) y x2.

Lemma or_to_orb : forall b1 b2 b3, Is_true (b1 || b2 || b3) <-> Is_true b1 \/ Is_true b2 \/ Is_true b3.
Proof. intros. split; intro H.
  + apply orb_prop_elim in H. destruct H. apply orb_prop_elim in H. intuition. intuition.
  + apply orb_prop_intro. destruct H. left. apply orb_prop_intro. now left.
    destruct H. left. apply orb_prop_intro. now right.
    now right.
Qed.

Program Instance B_PO_ex : @B_PO Bool_B CPO_valid_type :=
  {|
    weq x y := leq3 x y && leq3 y x;
    leq := leq3;
  |}.
Next Obligation.
  apply Build_PreOrder.
  + intro x. unfold leq3. repeat (apply orb_prop_intro; left).
    unfold eqbool. now destruct (eq_dec CPO_fin x x).
  + intros x y z Hxy Hyz. unfold leq3 in *.
    rewrite or_to_orb in *. intuition.
    - left. now apply eqbool_trans with y.
    - apply eqbool_refl in H, H1. rewrite H. rewrite H1. right. left.
      now apply eqbool_refl.
    - apply eqbool_refl in H0, H1. rewrite <- H0. rewrite H1. right. right.
      now apply eqbool_refl.
    - apply eqbool_refl in H1, H. rewrite H1 in H. inversion H.
Qed.
Next Obligation. split. apply andb_prop_elim. apply andb_prop_intro. Qed.


Instance leq3_refl : Reflexive (fun x y => Is_true (leq3 x y)).
  Proof. apply B_PO_ex_obligation_1. Qed.

Instance leq3_trans : Transitive (fun x y => Is_true (leq3 x y)).
  Proof. apply B_PO_ex_obligation_1. Qed.


Lemma weq_is_eq : forall (x y : CPO_set), 
  @weq_in_prop Bool_B CPO_valid_type B_PO_ex x y <-> x = y.
 Proof. split; intro H. destruct x, y; easy. now rewrite H. Qed.
 
 Lemma weq_is_eq2 : forall (x y : CPO_set), 
  Is_true (@weq Bool_B CPO_valid_type B_PO_ex x y) <-> x = y.
 Proof. apply weq_is_eq. Qed.

Definition sup_ex (D :@directed_set Bool_B CPO_valid_type leq3) := if (D x2) then x2 else (
              if (D x1) then x1 else bottom).

 Program Instance B_CPO_ex : B_CPO B_PO_ex :=
  {| 
     sup D := sup_ex D;
  |}.
  Next Obligation.
    split.
    + intros Hsupz y HDy. transitivity (sup_ex D); try assumption.
      destruct y. unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      unfold sup_ex in *. destruct (D x2).
      unfold leq3. apply or_to_orb. right. right. now apply eqbool_refl.
      destruct (D x1). reflexivity. contradict HDy.
      unfold sup_ex in *. destruct (D x2). reflexivity. contradict HDy.
    
    + intros. unfold sup_ex. destruct z.
      - destruct (D x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (D x1) eqn:EQ1. apply Is_true_eq_left in EQ1. apply (H x1 EQ1).
        reflexivity.
      - destruct (D x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (D x1) eqn:EQ1. reflexivity.
        unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      - unfold leq3. apply or_to_orb. right. right. reflexivity.
   Qed.


 Program Instance B_Lattice_ex : B_CL B_PO_ex :=
  {|
    Sup D := if (D x2) then x2 else (
              if (D x1) then x1 else bottom);
  |}.
  Next Obligation.
  split.
    + intros Hsupz y HDy. transitivity (if Y x2 then x2 else if Y x1 then x1 else bottom); try assumption.
      destruct y. unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      unfold sup_ex in *. destruct (Y x2).
      unfold leq3. apply or_to_orb. right. right. now apply eqbool_refl.
      destruct (Y x1). reflexivity. contradict HDy.
      unfold sup_ex in *. destruct (Y x2). reflexivity. contradict HDy.
    
    + intros. unfold sup_ex. destruct z.
      - destruct (Y x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (Y x1) eqn:EQ1. apply Is_true_eq_left in EQ1. apply (H x1 EQ1).
        reflexivity.
      - destruct (Y x2) eqn:EQ. apply Is_true_eq_left in EQ. apply (H x2 EQ).
        destruct (Y x1) eqn:EQ1. reflexivity.
        unfold leq3. apply or_to_orb. right. left. now apply eqbool_refl.
      - unfold leq3. apply or_to_orb. right. right. reflexivity.
  Defined.



  Program Definition F : CPO_set -> CPO_set := fun x => match x with
      | bottom => x2
      | x1 => x1
      | x2 => x2
    end.
 
  Lemma Increasing_F : is_true (@Increasing Bool_B CPO_valid_type B_PO_ex F).
  Proof. unfold Increasing. rewrite <- BForall_spec. intro x. destruct x; cbn; constructor. Qed.
 
 Definition P0_ex := (@P0 Bool_B CPO_valid_type B_PO_ex B_CPO_ex F).
 
 Definition P0' : (CPO_set -> bool) := fun x => (eqbool (X_fin := CPO_fin) x bottom || eqbool (X_fin := CPO_fin) x x2).
 
 Lemma P0'_is_invariant_subCPO : is_true (@Invariant Bool_B CPO_valid_type B_PO_ex F P0')
                              /\ is_true (@is_subCPO Bool_B CPO_valid_type B_PO_ex B_CPO_ex P0').
 Proof. split.
  + unfold Invariant. rewrite included_spec. intros x Hx. destruct x.
    unfold P0'. apply orb_prop_intro. now left. inversion Hx.
    unfold Image in Hx. rewrite <- BExists_spec in Hx. destruct Hx. rewrite <- BAnd_spec in H.
    destruct H as [HPx Hx2x]. rewrite weq_is_eq2 in Hx2x. rewrite Hx2x.
    destruct x; try easy.
  + apply is_subCPO_spec. intros D HDP. rewrite included_spec in HDP.
    cbn. unfold sup_ex. destruct (D x2) eqn:EQ.
    - setoid_rewrite EQ. apply HDP. now apply Is_true_eq_left in EQ.
    - setoid_rewrite EQ. destruct (D x1) eqn:EQ1. apply Is_true_eq_left in EQ1.
      pose proof (HDP x1 EQ1). contradict H.
      setoid_rewrite EQ1. easy.
  Qed.

 Lemma P0_is_P0' : is_true (@set_eq Bool_B CPO_valid_type P0_ex P0').
 Proof. unfold set_eq. apply BForall_spec. intro. apply BEq_spec. split; intro.
  + unfold P0_ex in H. rewrite <- P0_spec in H. apply (H P0'); try apply P0'_is_invariant_subCPO.
    intros. apply weq_is_eq in H0. now rewrite H0.
  + destruct x; unfold P0_ex; apply P0_spec.
    - intros Y Hi Hs HProper. rewrite <- is_subCPO_spec in Hs. apply (Hs empty). intuition.
    - inversion H.
    - intros Y Hi Hs HProper. unfold Invariant in Hi. rewrite included_spec in Hi.
      apply Hi. replace x2 with (F bottom). unfold Image. rewrite <- BExists_spec.
      exists bottom. rewrite <- BAnd_spec. split. rewrite <- is_subCPO_spec in Hs. now apply (Hs empty).
      reflexivity. now cbn.
  Qed.
  
  Lemma top_of_P0_is_x2 : Sup P0_ex = x2.
  Proof. simpl. destruct (P0_ex x2) eqn:EQ. reflexivity. exfalso.
    pose proof P0_is_P0'. unfold set_eq in H. rewrite <- BForall_spec in H. 
    specialize H with x2. rewrite <- BEq_spec in H. contradict EQ. 
    assert (P0_ex x2 = true). apply Is_true_eq_true. now apply H.
    rewrite H0. easy.
  Qed.
  
  Lemma top_of_P0_is_not_minimal : exists (a : CPO_set), is_greatest P0_ex a 
                                                      /\ ~ (is_least (@Fix Bool_B CPO_valid_type B_PO_ex F) a).
  Proof.
  exists (Sup P0_ex). split.
  + split.
      - rewrite top_of_P0_is_x2. pose proof P0_is_P0'. unfold set_eq in H. rewrite <- BForall_spec in H. 
        specialize H with x2. rewrite <- BEq_spec in H. now apply H. 
      - intros. now eapply leq_xSup.
    + intro. destruct H.
      rewrite top_of_P0_is_x2 in H0. specialize H0 with x1.
      assert (@is_true Bool_B (leq3 x2 x1)). apply H0. now cbn. inversion H1.
  Qed.
  
  
  
  (* ----- Testing computation of a minimal fixpoint ----- *)

  Program Definition Fmon : @mon Bool_B CPO_valid_type B_PO_ex := fun x => match x with
      | bottom => x1
      | x1 => x1
      | x2 => x2
    end.

Goal True.
set (x := @lfp_II Bool_B CPO_valid_type B_PO_ex B_CPO_ex Fmon).
simpl in x. unfold sup_ex in x. vm_compute in x.
(*Eval cbv in @gfp_II Bool_B CPO_valid_type B_PO_ex B_CPO_ex Fmon.*)

(* TODO : montrer que tout ordre partiel FINI est un CPO *)

End CPO_Examples.
