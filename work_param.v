From Coq Require Import Arith.
Require Import Psatz.
Require Export Setoid Morphisms.
Set Implicit Arguments.

Class B_param (B : Type) (X : Type) := {
  is_true : B -> Prop; (* need this to define everything *)
  BFalse : B; (* need this to define bottom in a CL *)
  BTrue : B; (* idem *)
  BFalse_spec : ~ (is_true BFalse);
  BTrue_spec : is_true BTrue;
  BAnd : B -> B -> B;
  BOr : B -> B -> B;
  BAnd_spec : forall b1 b2, is_true b1 /\ is_true b2 <-> is_true (BAnd b1 b2);
  BOr_spec : forall b1 b2, is_true b1 \/ is_true b2 <-> is_true (BOr b1 b2);
  BImpl : B -> B -> B;
  BImpl_spec : forall b1 b2, (is_true b1 -> is_true b2) <-> (is_true (BImpl b1 b2));
  BForall : (X -> B) -> B;
  BForall_spec : forall (P : X -> B), (forall x, is_true (P x)) <-> is_true (BForall P);
  BExists : (X -> B) -> B;
  BExists_spec : forall (P : X -> B), (exists x, is_true (P x)) <-> is_true (BExists P);
  
  (*
  BForall_g (A:Type) : (A -> B) -> (A -> B) -> B; (*here I is to select only a subset of A according to some condition B
    and bfun is the property that need to be true for all element in that subset *)
  BForall_g_spec : forall (A : Type) (I : A -> B) (bfun : A -> B),
                  (forall a, is_true (I a) -> is_true (bfun a)) <-> is_true (BForall_g I bfun);
  BExists_g (A : Type) : (A -> B) -> (A -> B) -> B;
  BExists_g_spec : forall (A : Type) (I : A -> B) (bfun : A -> B),
                  (exists a, is_true (I a) /\ is_true (bfun a)) <-> is_true (BExists_g I bfun);
  *)
  
  (*
  BForall : (B -> B) -> B; (* Prop ? Something else ? B*)
  BExists : (B -> B) -> B;
  BForall_spec : forall (SetB : B -> B), (forall b, is_true (SetB b) -> is_true b) 
                                         <-> is_true (BForall SetB);
  BExists_spec : forall (SetB : B -> B), (exists b, is_true (SetB b) /\ is_true b)
                                         <-> is_true (BExists SetB);
  *)
  
  (*PreOrder_leq:> PreOrder leq;*)
  (*B_impl : B -> B -> B;
  B_impl_trans : forall x y z, is_true (B_impl x y) -> is_true (B_impl y z) -> is_true (B_impl x z);*)
  }.

Class B_PO (X: Type) (B : Type) (Bp : B_param B X) := {
    weq: X -> X -> B;
    leq: X -> X -> B;
    weq_in_prop x y := is_true (weq x y);
    leq_in_prop x y := is_true (leq x y);
    Preorder_leq_in_prop :> PreOrder leq_in_prop;
    (*leq_refl : forall (x : X), leq_in_prop x x;
    leq_trans : forall x y z, leq_in_prop x y -> leq_in_prop y z -> leq_in_prop x z;*)
    weq_spec: forall x y, weq_in_prop x y <-> leq_in_prop x y /\ leq_in_prop y x;
  }.

(*
Definition weq_in_prop {X} {B} {Bp : B_param B} {L' : B_PO X Bp} (x y : X) := is_true (B := B) (weq x y).
Definition leq_in_prop {X} {B} {Bp : B_param B} {L' : B_PO X Bp} (x y : X) := is_true (B := B) (leq x y).
*)

(* Definition of Lattice as a particular (stronger) CPO. *)
Class B_CL (X : Type) (B : Type) (Bp : B_param B X) `(L' : B_PO X) := {
    sup: (X -> B) -> X;
    (*sup_spec0 : forall Y y, is_true (Y y) -> is_true (leq y (sup Y));*)
    sup_spec: forall Y z, leq_in_prop (sup Y) z <-> (forall y, is_true (Y y) -> leq_in_prop y z);
  }.

Declare Scope B_PO.
Open Scope B_PO.
Infix "==" := weq_in_prop (at level 70): B_PO.
Infix "<=" := leq_in_prop (at level 70): B_PO.
#[global] Hint Extern 0 => reflexivity: core.


Section Partial_order.

  Context {X} `{P' : B_PO X}.
(*
  #[global] Instance Preorder_leq : PreOrder leq_in_prop.
  Proof.
    constructor.
    intro x. apply leq_refl.
    intros x y z. apply leq_trans.
  Qed.
*)
  #[global] Instance Equivalence_weq: Equivalence weq_in_prop.
  Proof.
    constructor.
    intro x. now apply weq_spec.
    intros x y. rewrite 2weq_spec. tauto.
    intros x y z. rewrite 3weq_spec. split; transitivity y; tauto.
  Qed.

  #[global] Instance PartialOrder_weq_leq: PartialOrder weq_in_prop leq_in_prop.
  Proof.
    intros x y. cbn. now rewrite weq_spec.
  Qed.

End Partial_order.



Section sup.

  Context {X} {B} {Bp : B_param B X} {P' : B_PO Bp} {L : B_CL Bp P'}.

  Lemma leq_xsup (Y: X -> B) y : is_true (Y y) -> y <= sup Y.
  Proof. intro H. now apply (sup_spec Y). Qed.

  Definition bot := sup (fun _ => BFalse).
  
  Lemma bot_spec: forall x, bot <= x.
  Proof. intro. apply sup_spec. intros y Hy. contradict Hy. apply BFalse_spec. Qed.

  Definition top := sup (fun _ => BTrue).

  Lemma top_spec: forall x, x <= top.
  Proof. intro. apply leq_xsup. apply BTrue_spec. Qed.

  (** Inf *)

  Definition inf (Y : X -> B) := sup (fun z => BForall (fun y => BImpl (Y y) (leq z y))).
  Lemma inf_spec : forall Y z, z <= inf Y <-> (forall y, is_true (Y y) -> z <= y).
  Proof.
    intros. split.
    intros H y Yy. rewrite H. apply sup_spec. intros y0 H0.
    rewrite <- BForall_spec in H0. setoid_rewrite <- BImpl_spec in H0. now apply (H0 y).
    intro. apply leq_xsup. apply -> BForall_spec. intro y. apply -> BImpl_spec. intro. now apply H.
  Qed.

  Lemma leq_xinf (D: X -> B) y:  is_true (D y) -> inf D <= y.
  Proof. intro H. now apply inf_spec with D. Qed.

End sup.

#[global] Hint Resolve bot_spec: core.



Section function.

  Context {X} {B} {Bp : B_param B X} {P' : B_PO Bp}. 

  Record mon := { body:> X -> X; Hbody: Proper (leq_in_prop ==> leq_in_prop) body }.

  #[global] Instance Hbody' (F:mon) : Proper (weq_in_prop ==> weq_in_prop) F.
  Proof. intros x y Hxy. apply weq_spec. split; apply Hbody; now apply weq_spec in Hxy. Qed.

End function.



(* Knaster-Tarski Theorem on Lattices *)

Section lattice_results.
  Context {X} {B} {Bp : B_param B X} {P' : B_PO Bp} {L : B_CL Bp P'}.
  Variable b: mon.

  Definition gfp := sup (fun x => leq x (b x)).
  Definition lfp := inf (fun x => leq (b x) x).

  Proposition leq_gfp: forall y, y <= b y -> y <= gfp.
  Proof. apply leq_xsup. Qed.
  Proposition geq_lfp: forall y, b y <= y -> lfp <= y.
  Proof. apply leq_xinf. Qed.

  Lemma gfp_pfp: gfp <= b gfp.
  Proof.
    unfold gfp. apply sup_spec. intros y H. rewrite H. apply Hbody.
    apply leq_xsup. apply H.
  Qed.
  Lemma lfp_pfp: b lfp <= lfp.
  Proof.
    unfold lfp. apply inf_spec. intros y H. rewrite <- H. apply Hbody.
    apply leq_xinf. apply H.
  Qed.

  Lemma gfp_fp: gfp == b gfp.
  Proof.
    rewrite weq_spec. split.
    + apply gfp_pfp.
    + apply leq_xsup. apply Hbody. apply gfp_pfp.
  Qed.
  Lemma lfp_fp: lfp == b lfp.
  Proof.
    rewrite weq_spec. split.
    + apply leq_xinf. apply Hbody. apply lfp_pfp.
    + apply lfp_pfp.
  Qed.

End lattice_results.



Section Concrete_Examples.

Require Import Bool.


Program Instance Prop_B (X: Type): B_param Prop X :=
  {|
    is_true P := P;
    BTrue := True;
    BFalse := False;
    BAnd := and;
    BOr := or;
    BImpl P Q := P -> Q;
    BForall Px := forall (x:X), Px x;
    BExists Px := exists (x:X), Px x;
  |}.
  
  Check List.forallb.

  Context {A : Type}.
  Variable X : list A.
  Hypothesis HList : forall (a : A), List.In a X.

(* Bool on some X finite *)

Program Instance bool_B : B_param bool A :=
  {|
    is_true := Is_true;
    BTrue := true;
    BFalse := false;
    BAnd := andb;
    BOr := orb;
    BImpl := implb;
    BForall := fun P => List.forallb P X;
    BExists := fun P => List.existsb P X;
  |}.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation. destruct b1; destruct b2; intuition. Qed.
  Next Obligation.
    split; intro H. apply Is_true_eq_left. apply List.forallb_forall. 
    intros x Hx. apply Is_true_eq_true. apply H.
    intro x. apply Is_true_eq_left. apply Is_true_eq_true in H. rewrite List.forallb_forall in H.
    apply H. apply HList. Qed.
  Next Obligation.
    split; intro H. destruct H as [x Hx]. apply Is_true_eq_left. apply List.existsb_exists.
    exists x. split. apply HList. now apply Is_true_eq_true.
    apply Is_true_eq_true in H. apply List.existsb_exists in H. destruct H as [x Hx]. exists x.
    apply Is_true_eq_left. apply Hx. Qed.

End Concrete_Examples.


