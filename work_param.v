From Coq Require Import Arith.
Require Import Psatz.
Require Export Setoid Morphisms.
Set Implicit Arguments.

Section B.

Class B_param (B : Type) := {
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
  }.

Definition BEq `{B_param} PB1 PB2 := BAnd (BImpl PB1 PB2) (BImpl PB2 PB1).
Lemma BEq_spec `{B_param} : forall b1 b2, (is_true b1 <-> is_true b2) <-> is_true (BEq b1 b2).
Proof. intros b1 b2. setoid_rewrite <- BAnd_spec. setoid_rewrite <- BImpl_spec. tauto. Qed.

Definition BEq_in_prop `{B_param} PB1 PB2 := is_true (BEq PB1 PB2).

#[global] Instance trans_Impl `{B_param} : Transitive (fun b1 b2 => is_true (BImpl b1 b2)).
Proof. intros b1 b2 b3. setoid_rewrite <- BImpl_spec. tauto. Qed.
#[global] Instance refl_Impl `{B_param} : Reflexive (fun b1 b2 => is_true (BImpl b1 b2)).
Proof. intro b1. setoid_rewrite <- BImpl_spec. tauto. Qed.

Class B_param_plus (B : Type) (X : Type) `(B_param B) := {
  BForall : (X -> B) -> B;(*Needed for Inf, for comparison of monotonous functions, and for set equality.*)
  BForall_spec : forall (P : X -> B), (forall x, is_true (P x)) <-> is_true (BForall P);
  BExists : (X -> B) -> B; (*Needed for Images of functions and monotonous complete lattice*)
  BExists_spec : forall (P : X -> B), (exists x, is_true (P x)) <-> is_true (BExists P);
  BForall_set : ((X -> B) -> B) -> B; (* Needed for definition of P0 *)
  BForall_set_spec : forall (P : (X -> B) -> B), (forall Y, is_true (P Y)) <-> is_true (BForall_set P);
  BExists_set : ((X -> B) -> B) -> B; (*needed for the Complete Lattice of parts/subsets, and definition of P0*)
  BExists_set_spec : forall (P : (X -> B) -> B), (exists S, is_true (P S)) <-> is_true (BExists_set P);
  
  BExists_fun : ((X -> X) -> B) -> B;
  BExists_fun_spec : forall (P : (X -> X) -> B), (exists f, is_true (P f)) <-> is_true (BExists_fun P);
  
  
  BExists_nat : (nat -> B) -> B;
  BExists_nat_spec : forall (P : nat -> B), (exists n, is_true (P n)) <-> is_true (BExists_nat P);
  (*
  BForall_g (A:Type) : (A -> B) -> (A -> B) -> B; (*here I is to select only a subset of A according to some condition B
    and bfun is the property that need to be true for all element in that subset *)
  BForall_g_spec : forall (A : Type) (I : A -> B) (bfun : A -> B),
                  (forall a, is_true (I a) -> is_true (bfun a)) <-> is_true (BForall_g I bfun);
  BExists_g (A : Type) : (A -> B) -> (A -> B) -> B;
  BExists_g_spec : forall (A : Type) (I : A -> B) (bfun : A -> B),
                  (exists a, is_true (I a) /\ is_true (bfun a)) <-> is_true (BExists_g I bfun);
  *)
  }.

End B.

Ltac unfold_spec := try repeat (setoid_rewrite <- BAnd_spec)
                            || (setoid_rewrite <- BOr_spec)
                            || (setoid_rewrite <- BImpl_spec)
                            || (setoid_rewrite <- BForall_spec)
                            || (setoid_rewrite <- BExists_spec)
                            || (setoid_rewrite <- BForall_set_spec)
                            || (setoid_rewrite <- BExists_set_spec)
                            || (setoid_rewrite <- BExists_fun_spec).

Section CPO_CL.

Context {X : Type} {B} {Bp : B_param B} {Bpp : B_param_plus X Bp}.

Notation set := (X -> B).
Notation rel := (X -> X -> B).
(*
Definition weq_in_prop `(weq : rel) (x y : X) := is_true (weq x y).
Definition leq_in_prop `(leq : rel) (x y : X) := is_true (leq x y).
Definition Directed `(leq_in_prop : X -> X -> Prop) (D : set) : Prop :=
  forall x y, is_true (D x) -> is_true (D y) -> exists z, is_true (D z) /\ leq_in_prop x z /\ leq_in_prop y z.
Definition directed_set `(leq_in_prop : X -> X -> Prop) := 
  {Dbody : set | Directed leq_in_prop Dbody}.
Definition Dbody `(leq_in_prop : X -> X -> Prop) (D : directed_set leq_in_prop) : set := 
  proj1_sig D.
  *)

Class B_PO := {
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

Definition Directed (leq : X -> X -> B) (D : set) : B := 
  BForall (fun x => BForall (fun y => BImpl (D x) (BImpl (D y) 
    (BExists (fun z => BAnd (D z) (BAnd (leq x z) (leq y z))))))).
Definition Directed_in_prop leq D := is_true (Directed leq D).
Lemma Directed_spec (leq : X -> X -> B) (D : set) : (forall x y, is_true (D x) -> is_true (D y) -> 
    exists z, is_true (D z) /\ is_true (leq x z) /\ is_true (leq y z))
  <-> is_true (Directed leq D).
Proof.
  repeat setoid_rewrite <- BForall_spec. repeat setoid_rewrite <- BImpl_spec.
  setoid_rewrite <- BExists_spec. repeat setoid_rewrite <- BAnd_spec. unfold leq_in_prop. tauto.
Qed.
Definition directed_set `(leq : X -> X -> B) := {Dbody : set | Directed_in_prop leq Dbody}.
Definition Dbody `(leq : X -> X -> B) (D : directed_set leq) : set := proj1_sig D.
Coercion Dbody : directed_set >-> Funclass.

Class B_CPO `(P' : B_PO) := {
    sup: directed_set leq -> X;
    sup_spec: forall D z, (leq_in_prop (sup D) z <-> forall (y:X), is_true ((Dbody D) y) -> leq_in_prop y z);
  }.

(* Definition of Lattice as a particular (stronger) CPO. *)
Class B_CL `(L' : B_PO) := {
    Sup: (X -> B) -> X;
    (*sup_spec0 : forall Y y, is_true (Y y) -> is_true (leq y (sup Y));*)
    Sup_spec: forall Y z, leq_in_prop (Sup Y) z <-> (forall y, is_true (Y y) -> leq_in_prop y z);
  }.
  (* Convention : capital letters for CL from now on. *)


Class B_param_dir (B : Type) (X : Type) `(B_param B) `(P : B_PO) := {
  BForall_directed_set : (directed_set leq -> B) -> B; (* Needed to define the subCPO property *)
  BForall_directed_set_spec : forall (P : directed_set leq -> B), (forall Y, is_true (P Y)) <-> is_true (BForall_directed_set P);
}.

End CPO_CL.

Declare Scope B_PO.
Open Scope B_PO.
Infix "==" := weq_in_prop (at level 70): B_PO.
Infix "<=" := leq_in_prop (at level 70): B_PO.
#[global] Hint Extern 0 => reflexivity: core.



Ltac fold_leq := match goal with
  | |- context [is_true (leq ?x ?y)] => fold (leq_in_prop x y)
end.
Ltac fold_weq := match goal with
  | |- context [is_true (weq ?x ?y)] => fold (weq_in_prop x y)
end.


Section Concrete_Examples.
(*
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
*)
End Concrete_Examples.

(*
(** * Sets general properties *)

Section Sets.

  Context {X} `{P' : B_PO X}.

  Definition set_eq (f g : X -> Prop) := forall z, f z <-> g z. (*equality of sets*)

  Definition included (S T: X -> B) := forall x, is_true (BImpl (S x) (T x)).

  #[global] Instance Included_trans : Transitive included.
  Proof. intros Y1 Y2 Y3 H12 H13 x. now apply (trans_Impl (Y1 x)) with (Y2 x). Qed.

End Sets.
Infix "⊆" := included (at level 70).
*)


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
  
  Record mon := { body:> X -> X; Hbody: Proper (leq_in_prop ==> leq_in_prop) body }.
  
   Program Definition const x: mon := {| body y := x |}.
  Next Obligation. intros ? ? ?. reflexivity. Qed.

  Definition id: mon := {|
                         body x := x;
                         Hbody x y H := H
                       |}.

  Definition comp (f g: mon): mon :=
    {|
      body := fun x => f (g x);
      Hbody x y H := Hbody f _ _ (Hbody g _ _ H)
    |}.

End Partial_order.
Infix "°" := comp (at level 20): B_PO.


Section sup.

  Context {X} {B} {Bp : B_param B} {Bpp : B_param_plus X Bp} {P' : B_PO (X := X)} {P : B_CPO P'} {L : B_CL P'}.

  Lemma leq_xsup (D: directed_set leq) (y : X) : is_true (D y) -> y <= sup D.
  Proof. intro H. now apply (sup_spec D). Qed.
  Lemma leq_xSup (Y: X -> B) (y : X) : is_true (Y y) -> y <= Sup Y.
  Proof. intro H. now apply (Sup_spec Y). Qed.

  Program Definition empty : directed_set leq :=
    exist _ (fun _ => BFalse) _.
  Next Obligation. unfold Directed_in_prop. apply Directed_spec. intros. contradict H. apply BFalse_spec. Defined.

  Definition bot := sup empty.
  Definition Bot := Sup (fun _ => BFalse). (* CompleteLattice Bot *)
  (* Rmk : insteaf of working with notions from CPO and CL alike, we could just turn a CL into a CPO,
  but for basic notion like this, it might be better to have both *)
  
  Lemma bot_spec : forall x, bot <= x.
  Proof. intro. apply sup_spec. intros y Hy. contradict Hy. apply BFalse_spec. Qed.
  Lemma Bot_spec: forall x, Bot <= x.
  Proof. intro. apply Sup_spec. intros y Hy. contradict Hy. apply BFalse_spec. Qed.

  Definition Top := Sup (fun _ => BTrue).

  Lemma Top_spec: forall x, x <= Top.
  Proof. intro. apply leq_xSup. apply BTrue_spec. Qed.

  (** Inf *)

  Definition Inf (Y : X -> B) := Sup (fun z => BForall (fun y => BImpl (Y y) (leq z y))).
  Lemma Inf_spec : forall Y z, z <= Inf Y <-> (forall y, is_true (Y y) -> z <= y).
  Proof.
    intros. split.
    intros H y Yy. rewrite H. apply Sup_spec. intros y0 H0.
    rewrite <- BForall_spec in H0. setoid_rewrite <- BImpl_spec in H0. now apply (H0 y).
    intro. apply leq_xSup. apply -> BForall_spec. intro y. apply -> BImpl_spec. intro. now apply H.
  Qed.

  Lemma leq_xInf (D: X -> B) y:  is_true (D y) -> Inf D <= y.
  Proof. intro H. now apply Inf_spec with D. Qed.

End sup.

#[global] Hint Resolve bot_spec: core.
#[global] Hint Resolve Bot_spec: core.



(* Knaster-Tarski Theorem on Lattices *)

Section lattice_results.
  Context {X} {B} {Bp : B_param B} {P' : B_PO (X := X)} {L : B_CL P'}.
  Context {Bpp : B_param_plus X Bp}.
  Variable b: mon.

  Definition gfp := Sup (fun x => leq x (b x)).
  Definition lfp := Inf (fun x => leq (b x) x).

  Proposition leq_gfp: forall y, y <= b y -> y <= gfp.
  Proof. apply leq_xSup. Qed.
  Proposition geq_lfp: forall y, b y <= y -> lfp <= y.
  Proof. apply leq_xInf. Qed.

  Lemma gfp_pfp: gfp <= b gfp.
  Proof.
    unfold gfp. apply Sup_spec. intros y H. rewrite H. apply Hbody.
    apply leq_xSup. apply H.
  Qed.
  Lemma lfp_pfp: b lfp <= lfp.
  Proof.
    unfold lfp. apply Inf_spec. intros y H. rewrite <- H. apply Hbody.
    apply leq_xInf. apply H.
  Qed.

  Lemma gfp_fp: gfp == b gfp.
  Proof.
    rewrite weq_spec. split.
    + apply gfp_pfp.
    + apply leq_xSup. apply Hbody. apply gfp_pfp.
  Qed.
  Lemma lfp_fp: lfp == b lfp.
  Proof.
    rewrite weq_spec. split.
    + apply leq_xInf. apply Hbody. apply lfp_pfp.
    + apply lfp_pfp.
  Qed.

End lattice_results.



Section function.

  Context {X} {B} {Bp : B_param B} {Bpp : B_param_plus X Bp}  {P' : B_PO (X := X)} {P : B_CPO P'}.

  Definition Fix F x := weq (F x) x.
  Definition Post F x := leq x (F x).
  Definition Pre F x := leq (F x) x.

  Lemma fix_is_post F : forall x, is_true (Fix F x) -> is_true (Post F x).
  Proof. intros. apply weq_spec in H. apply H. Qed.
  Lemma fix_is_pre F : forall x, is_true (Fix F x) -> is_true (Pre F x).
  Proof. intros. apply weq_spec in H. apply H. Qed.

  #[global] Instance Hbody' (F:mon) : Proper (weq_in_prop ==> weq_in_prop) F.
  Proof. intros x y Hxy. apply weq_spec. split; apply Hbody; now apply weq_spec in Hxy. Qed.

  Definition Image f (S : X -> B) y := (BExists (fun x => BAnd (S x) (weq y (f x)))).

  Definition Continuous f :=
    forall (D : X -> B) (H : is_true (Directed leq D)),
      {dir_im : is_true (Directed leq (Image f D)) &
                f (sup (exist _ D H )) == sup (exist _ (Image f D) dir_im)}.

  Lemma mon_preserves_directedness_and_sup (F:mon) :
    forall (D : X -> B) (H : is_true (Directed leq D)),
      {dir_im : is_true (Directed leq (Image F D)) &
                  sup (exist _ (Image F D) dir_im) <= F (sup (exist _ D H ))}.
  Proof.
    intros. assert (is_true (Directed leq (Image F D))) as DD.
    + apply Directed_spec. intros y1 y2 Hfy1 Hfy2. apply BExists_spec in Hfy1, Hfy2. 
      destruct Hfy1 as [x1 Hx1]. destruct Hfy2 as [x2 Hx2].
      apply BAnd_spec in Hx1, Hx2. destruct Hx1 as [Dx1 Hx1]. destruct Hx2 as [Dx2 Hx2].
      rewrite <- Directed_spec in H.
      destruct (H x1 x2) as [x Hx]; try assumption.
      exists (F x). repeat split. apply BExists_spec. exists x. apply BAnd_spec. split.
      apply Hx. fold_weq. reflexivity. fold_leq. fold (weq_in_prop y1 (F x1)) in Hx1.
      apply weq_spec in Hx1. destruct Hx1 as [Hx1 _]. transitivity (F x1).
      apply Hx1. apply Hbody. apply Hx. fold (weq_in_prop y2 (F x2)) in Hx2. fold_leq.
      transitivity (F x2). now apply weq_spec in Hx2. now apply Hbody.
    + exists DD. apply sup_spec; cbn. intros y Hy.
      apply BExists_spec in Hy. destruct Hy as [x Hx]. apply BAnd_spec in Hx. destruct Hx as [Dx Hx].
      rewrite Hx. apply Hbody. now apply leq_xsup.
  Qed.

(* Iterations of a function *)


  Definition foo (x:X) (f : {x = bot} + {x <> bot}) : Prop := match f with | left _ => True | right _ => False end.

(*
  Fixpoint iteres F (y : X) (is_bot_y : {y = bot} + {y <> bot}) : B := match is_bot_y with
  | left _ => BTrue
  | right _ => BExists (fun x => BAnd (weq y (F x)) (iteres F x))
  end.
  
  | iteres_0 : (iteres F bot)
  | iteres_S : forall x, (iteres F x) -> (iteres F (F x)).

*)
  Fixpoint itere F n x0 : X :=
    match n with
    | 0 => x0
    | S m => F (itere F m x0)
    end. (*Indexed by n for simplicity on comparison properties.*)

  Lemma itere_monotony (F:mon) : forall n, Proper (leq_in_prop ==> leq_in_prop) (itere F n).
  Proof. intros n x y H. induction n. now cbn. cbn. now apply Hbody. Qed.

  Lemma chain_itere (F:mon) : forall (n : nat), itere F n bot <= itere F (S n) bot.
  Proof. intro n. induction n. now cbn. cbn. now apply Hbody. Qed.

  Lemma chain_increase (F:mon) : forall (m n : nat), le n m -> itere F n bot <= itere F m bot.
  Proof.
    intros m n H. induction m. now inversion H.
    inversion H. easy.
    rewrite <- chain_itere. now apply IHm.
  Qed.

  Lemma itere_preserves_fix (F:mon) : forall β n, is_true (Fix F β) -> (itere F n β) == β.
  Proof.
    intros. induction n. now cbn. cbn. unfold Fix in H. rewrite <- H at 2.
    now apply Hbody'.
  Qed.

  Definition iteres F x : B := BExists_nat (fun n => weq x (itere F n bot)).

(* TODO !
  Definition iteres F : X -> B :=
  | from_bot : forall n, iteres F (itere F n bot).

  Lemma iteres_directed (F:mon): Directed (iteres F).
  Proof.
    unfold Directed. intros. destruct H. destruct H0.
    destruct le_ge_dec with n n0.
    + exists (itere F n0 bot). repeat split. now apply chain_increase. reflexivity.
    + exists (itere F n bot). repeat split. reflexivity. now apply chain_increase.
  Qed.

  Variant iteres_from_1 F : X -> Prop :=
  | from_bot_from_1 : forall n, le 1 n -> iteres_from_1 F (itere F n bot).

  Lemma iteres_from_1_directed (F:mon): Directed leq (iteres_from_1 F).
  Proof.
    unfold Directed. intros. destruct H. destruct H0.
    destruct le_ge_dec with n n0.
    + exists (itere F n0 bot). repeat split. assumption. now apply chain_increase. reflexivity.
    + exists (itere F n bot). repeat split. assumption. reflexivity. now apply chain_increase.
  Qed.

  Lemma image_of_iteres F : set_eq (Image F (iteres F)) (iteres_from_1 F).
  Proof.
    intro. split; intro; inversion H. inversion H0.
    + assert (iteres_from_1 F (itere F (S n) bot)). apply from_bot_from_1. lia.
      apply H3.
    + induction n. contradict H0. lia.
      cbn. apply from_image. apply from_bot.
  Qed.

  Lemma from_1_included F : included (iteres_from_1 F) (iteres F).
  Proof. intros x H. inversion H. apply from_bot. Qed.
*)
End function.



(** * Sets general properties *)

Section Sets.

  Context {X} {B} {Bp : B_param B} {P' : B_PO (X := X)}.
  Context {Bpp : B_param_plus X Bp}.

  Definition set_eq (f g : X -> B) :=  (BForall (B_param_plus := Bpp)) (fun z => (BEq (f z) (g z))). (*equality of sets*)

  Definition included (S T: X -> B) := BForall (B_param_plus := Bpp) (fun x => (BImpl (S x) (T x))).
  Lemma included_spec (S T : X -> B) : is_true (included S T) <-> forall x, is_true (S x) -> is_true (T x).
  Proof. setoid_rewrite <- BForall_spec. now setoid_rewrite <- BImpl_spec. Qed.
  
  Definition included_prop (S T : X -> B) := is_true (included S T).
  
End Sets.
Infix "⊆" := included_prop (at level 70).




Section Particular_CPOs.

  Context {X} {B} {Bp : B_param B} {Bpp : B_param_plus X Bp} {P' : B_PO (X := X)} {P : B_CPO P'}.
  Context {Bpp_mon : B_param_plus mon Bp}.

 Program Instance B_PO_mon : @B_PO mon B Bp :=
    {|
      weq f g := BForall (fun (x:X) => weq (f x) (g x));
      leq f g := BForall (fun (x:X) => leq (f x) (g x));
    |}.
  Next Obligation.
  apply Build_PreOrder.
    + intro x. apply BForall_spec. intro. fold_leq. reflexivity.
    + intros f g h Hfg Hgh. apply BForall_spec. intro x. fold_leq.
      rewrite <- BForall_spec in Hfg, Hgh.
      transitivity (g x). apply Hfg. apply Hgh.
  Qed.
  Next Obligation.
    setoid_rewrite <- BForall_spec.
    split; intros.
    + split; intro a; apply weq_spec. symmetry; apply H. apply H.
    + apply weq_spec. split; apply H.
  Qed.

  Program Instance B_CPO_mon : B_CPO B_PO_mon :=
    {|
      sup (F : @directed_set mon B Bp Bpp_mon leq) := {| body x := sup (fun y => BExists (*B mon Bp Bpp_mon*) (fun f => BAnd (F f) (weq y (f x)))) |};
    |}.
  Next Obligation.
    apply Directed_spec. repeat setoid_rewrite <- BExists_spec.
    intros. destruct F as [SF D]; cbn in *. setoid_rewrite <- Directed_spec in D.
    destruct H as [fx Hfx]. destruct H0 as [fy Hfy]. rewrite <- BAnd_spec in Hfx, Hfy.
    destruct Hfx as [Hfx Eqfx]. destruct Hfy as [Hfy Eqfy].
    destruct (D fx fy) as [f [Hf1S [Hff1 Hff2]]]; try assumption.
    exists (f x). unfold leq_in_prop in Hff1, Hff2. cbn in *. rewrite <- BForall_spec in Hff1, Hff2.
    repeat split. exists f. apply BAnd_spec. split. 
    assumption. fold_weq. reflexivity.
                                 + fold (leq_in_prop x0 (f x)). transitivity (fx x).
                                   apply weq_spec in Eqfx. apply Eqfx. apply (Hff1 x).
                                 + fold (leq_in_prop y (f x)). transitivity (fy x).
                                   apply weq_spec in Eqfy. apply Eqfy. apply (Hff2 x).
  Qed.
  Next Obligation.
    destruct F as [SF D]; cbn in *.
    intros x y H. apply sup_spec; cbn. intros.
    rewrite <- BExists_spec in H0. setoid_rewrite <- BAnd_spec in H0.
    destruct H0 as [f [Hfx0 Eqyx]].
    transitivity (f y). rewrite Eqyx. now apply Hbody.
    apply leq_xsup. cbn. apply BExists_spec. exists f. apply BAnd_spec.
    split. assumption. fold_weq. reflexivity.
  Qed.
  Next Obligation.
    destruct D as [SF D]; cbn in *. split.
    + intros H f Df. unfold leq_in_prop in *. cbn in *. rewrite <- BForall_spec in *. intro x.
      fold_leq. rewrite <- H.
      eapply sup_spec. reflexivity. cbn. apply BExists_spec. exists f. apply BAnd_spec. split. assumption.
      now fold_weq.
    + intro H. unfold leq_in_prop. cbn. apply BForall_spec. intro x. apply sup_spec. cbn. intros y Hy.
      rewrite <- BExists_spec in Hy. destruct Hy as [f Hf]. apply BAnd_spec in Hf. destruct Hf as [Hf Eqyfx].
      rewrite Eqyfx. unfold leq_in_prop in H. cbn in H. setoid_rewrite <- BForall_spec in H. now apply (H f).
  Qed.

  Program Instance B_PO_parts: @B_PO (X -> B) B Bp :=
    {|
      weq := set_eq;
      leq := included;
    |}.
  Next Obligation.
    apply Build_PreOrder.
    + intro Y. apply BForall_spec. intro x. apply refl_Impl.
    + intros S T U. setoid_rewrite <- BForall_spec. intros. now apply (trans_Impl (S x)) with (T x).
  Qed.
  Next Obligation.
    setoid_rewrite <- BForall_spec. setoid_rewrite <- BEq_spec. setoid_rewrite <- BImpl_spec.
    intuition; now apply H.
  Qed.
 
  Context {Bpp_part : B_param_plus (X -> B) Bp}.

  Program Instance B_CPO_parts: B_CPO B_PO_parts :=
    {|
      sup A := (fun x => BExists_set (fun Y => BAnd (A Y) (Y x)));
    |}.
  Next Obligation.
    unfold leq_in_prop; cbn. split; intros. 
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro Hx.
      setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BImpl_spec in H. 
      setoid_rewrite <- BExists_set_spec in H. apply (H x). exists y. apply BAnd_spec. now split.
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro PDx. 
      rewrite <- BExists_set_spec in PDx. setoid_rewrite <- BAnd_spec in PDx. destruct PDx as [S [Ds Sx]].
      specialize H with S. apply H in Ds. setoid_rewrite <- BForall_spec in Ds. setoid_rewrite <- BImpl_spec in Ds.
      now apply Ds.
  Qed.

  Program Instance Lattice_parts : B_CL (B_PO_parts) :=
    {|
      Sup A := (fun x => BExists_set (fun Y => BAnd (A Y) (Y x)));
    |}.
+++++++++++  Next Obligation.
   unfold leq_in_prop; cbn. split; intros. 
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro Hx.
      setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BImpl_spec in H. 
      setoid_rewrite <- BExists_set_spec in H. apply (H x). exists y. apply BAnd_spec. now split.
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro PDx. 
      rewrite <- BExists_set_spec in PDx. setoid_rewrite <- BAnd_spec in PDx. destruct PDx as [S [Ds Sx]].
      specialize H with S. apply H in Ds. setoid_rewrite <- BForall_spec in Ds. setoid_rewrite <- BImpl_spec in Ds.
      now apply Ds.
   Qed.

  Context {Bpd : B_param_dir B Bp P'}.

(** * sub-CPO : Define a set (part of X) as being a CPO *)

  Definition is_subCPO (Y : X -> B) :=   
    BForall_directed_set (fun D => (BImpl (included D Y) (Y (sup D)))).
  Lemma is_subCPO_spec Y : (forall (D : directed_set _),
      is_true (included D Y) -> is_true (Y (sup D))) <-> is_true (is_subCPO Y).
  Proof.
    setoid_rewrite <- BForall_directed_set_spec. repeat setoid_rewrite <- BImpl_spec.
    tauto.
  Qed.

  Definition down (x:X) := (fun z => leq z x).

  Lemma down_is_subCPO : forall x, is_true (is_subCPO (down x)).
  Proof. setoid_rewrite <- is_subCPO_spec. intros x D Hd. unfold down. apply sup_spec.
   intros. rewrite included_spec in Hd. now apply Hd. Qed.


(* Doesn't work : requires dependent pair in B :'( *)

(*
  Definition set_type (Y : X -> B) : Type := { x : X | is_true (Y x)}.
  Definition element Y (y :set_type Y) := proj1_sig y.
  #[global] Coercion element : set_type >-> X.

  Definition complete_body {Y : X -> B} (D : (set_type Y) -> B) : X -> B :=
    (fun x => {is_in_Y : is_true (Y x) & (D (exist _ x is_in_Y))}).
    
  Program Instance subPO (Y:set X) : (PO (set_type Y)) :=
    {|
      weq x y := (@weq X P') x y;
      leq x y := (@leq X P') x y;
    |}.
  Next Obligation. apply Build_PreOrder; intro x. reflexivity. intros y z Hxy Hyz. now transitivity y. Qed.
  Next Obligation. apply weq_spec. Qed.

  Program Instance subCPO (Y:set X) (H : is_subCPO Y) : (CPO (subPO Y)) :=
    {|
      sup D := sup (exist (Directed leq) (complete_body D) _) ;
    |}.
  Next Obligation.
    destruct D as [D Hd]. cbn. intros x y Hx Hy. inversion Hx. inversion Hy.
    destruct (Hd (exist (fun x : X => Y x) x x0) (exist (fun x : X => Y x) y x1))
      as [[z Pz] [Hz [Hxz Hyz]]]; try assumption.
    exists z. split. now exists Pz. now split.
  Qed.
  Next Obligation.
    apply H. intros x Hx.
    destruct D as [D Hd]; cbn in Hx. now destruct Hx.
  Qed.
  Next Obligation.
    split.
    + intros. apply (sup_spec (exist (Directed leq) (complete_body D) (subCPO_obligation_1 D))); cbn.
      assumption. destruct y. cbn.
      now exists y.
      + intros. apply sup_spec. cbn. intros. destruct H1. now apply (H0 (exist (fun x : X => Y x) y x)).
  Qed.
*)

  (* Some instances that can now be defined on CPO_parts and CPO_mon. *)

  Variable F : X -> X.

  #[global] Instance image_eq : Proper (@weq_in_prop (X -> B) B Bp B_PO_parts ==> weq_in_prop) (Image F).
  Proof. intros Y1 Y2 HY. apply weq_spec. unfold Image. unfold leq_in_prop. cbn. setoid_rewrite included_spec.
   setoid_rewrite <- BExists_spec. setoid_rewrite <- BAnd_spec. split; intros x H; destruct H as [y [Hy Hxy]];
   exists y; apply weq_spec in HY; destruct HY as [Y12 Y21]; unfold leq_in_prop in Y12, Y21; cbn in *; rewrite included_spec in Y12, Y21;
   split. now apply Y12. assumption. now apply Y21. assumption.
 Qed.

  #[global] Instance set_incl : Proper (@weq_in_prop (X -> B) B Bp B_PO_parts ==> weq_in_prop ==> BEq_in_prop) included.
  Proof. intros Y1 Y2 H12 Y3 Y4 H34. apply BEq_spec. setoid_rewrite included_spec.
   apply weq_spec in H12, H34. destruct H12 as [H12 H21]. destruct H34 as [H34 H43].
   unfold leq_in_prop in *; cbn in *. rewrite included_spec in H12, H21, H34, H43. intuition.
  Qed.

  Lemma set_equivalent : forall (f g : X -> B), f == g -> (pointwise_relation X BEq_in_prop) f g.
  Proof.
    intros f g H x. apply BEq_spec. apply weq_spec in H.
    unfold leq_in_prop in *; cbn in *. setoid_rewrite included_spec in H. intuition.
  Qed.

End Particular_CPOs.


(** * Invariant subCPOs *)

Section Invariant_subCPOs.

  Context {X} {B} {Bp : B_param B} {Bpp : B_param_plus X Bp} {P' : B_PO (X := X)} {P : B_CPO P'}.
  Context  {Bpp_mon : B_param_plus mon Bp} {Bpd : B_param_dir B Bp P'}.

  Definition Invariant (F : X -> X) Y := included (Image F Y) Y.

  Variable F : X -> X.

  Definition P0 x :=  (*P0 is the smallest invariant subCPO : intersection of all invariant sub_CPOs.*)
    BForall_set (fun Y => BImpl (Invariant F Y) (BImpl (is_subCPO Y) (Y x))).
  Hypothesis fun_ext : forall x y, x == y -> is_true (P0 x) <-> is_true (P0 y). (* need functional extensionality *)
  
  Lemma P0_spec : forall x, (forall Y, is_true (Invariant F Y) -> is_true (is_subCPO Y) -> is_true (Y x)) <-> is_true (P0 x).
  Proof. setoid_rewrite <- BForall_set_spec. repeat setoid_rewrite <- BImpl_spec. tauto. Qed.

  Lemma P0_is_invariant_subCPO : is_true (Invariant F P0) /\ is_true (is_subCPO P0).
  Proof.
    split.
    + apply BForall_spec. setoid_rewrite <- BImpl_spec. intros x H.
      unfold Image in H. rewrite <- BExists_spec in H. destruct H as [x0 H]. rewrite <- BAnd_spec in H.
      apply fun_ext with (F x0). apply H. rewrite <- P0_spec. intros Y Hi Hs. destruct H. rewrite <- P0_spec in H.
      unfold Invariant in Hi. rewrite included_spec in Hi. apply Hi. apply BExists_spec. exists x0.
      apply BAnd_spec. split. apply H. apply included_spec. apply Hi. apply Hs.
      now fold_weq.
    + apply is_subCPO_spec. intros D H. rewrite <- P0_spec. intros Y Hi Hs. rewrite <- is_subCPO_spec in Hs. apply Hs.
      rewrite included_spec. rewrite included_spec in H. intros x Hx. specialize H with x. 
      apply H in Hx. rewrite <- P0_spec in Hx. apply Hx. apply Hi. apply is_subCPO_spec. apply Hs.
  Qed.

  Lemma P0_is_smallest_invariant_subCPO : forall Y, is_true (Invariant F Y) -> is_true (is_subCPO Y) -> is_true (included P0 Y).
  Proof. intros Y Hi Hs. apply included_spec. intros x Hx. rewrite <- P0_spec in Hx. now apply Hx. Qed.

End Invariant_subCPOs.



(** * Common fixpoint of every monotonous increasing function *)

Section Increasing_fixpoint.
  Context {X} {B} {Bp : B_param B} {Bpp : B_param_plus X Bp} {P' : B_PO (X := X)} {P : B_CPO P'}.
  Context  {Bpp_mon : B_param_plus mon Bp}.

  Definition Increasing F := @BForall B X Bp Bpp (fun x => leq x (F x)).
  Definition Increasing_restricted Y F := BAnd (Invariant F Y) (@BForall B X Bp Bpp (fun x => BImpl (Y x) (leq x (F x)))).
  (* Note : this definition might cause some problems when Y is not F-Invariant, 
     but it is simpler to define it that way *)

  Definition leq_mon f g := (@leq mon B Bp B_PO_mon f g).
  Definition weq_mon f g := (@weq mon B Bp B_PO_mon f g).

  Program Definition Increasing_functions := exist (Directed_in_prop (Bp := Bp) leq_mon) (Increasing) _.
  Next Obligation.
    apply Directed_spec. unfold_spec. intros f g Hf Hg. exists (comp f g). (*destruct Hg as [Invg Subg]. destruct Hf as [Invf Subf].*)
    (*setoid_rewrite <- BForall_spec in Hf. setoid_rewrite <- BForall_spec in Hg.*)
    repeat split. (*apply BForall_spec.*)
    (*+ intros x HYfgx. destruct HYfgx as [x0 [Yx0 fgx]].
      apply Invf. exists (g x0). split; try assumption.
      apply Invg. exists x0. split; try assumption. fold (weq_in_prop (g x0) (g x0)). reflexivity.*)
    + intros x. fold_leq. transitivity (g x). apply Hg. apply Hf. (*now apply Subg. apply Subf.
      apply Invg. exists x. split; try assumption. fold (weq_in_prop (g x) (g x)). reflexivity.*)
    + cbn. apply BForall_spec. intro x. apply Hbody. apply Hg.
    + cbn. apply BForall_spec. intro x. cbn. apply Hf.
  Defined.

  Definition H_sup := (sup (B_CPO := B_CPO_mon) Increasing_functions).

  Lemma H_sup_is_increasing : is_true (Increasing H_sup).
  Proof. apply BForall_spec. intro. assert (is_true (leq_mon id H_sup)).
   apply (sup_spec (B_CPO := B_CPO_mon) Increasing_functions). reflexivity.
   unfold Increasing_functions. cbn. apply BForall_spec. intro.
   now fold_leq.
   cbn in H. rewrite <- BForall_spec in H. apply H. 
  Qed.

  Lemma H_sup_bot_is_fixpoint_of_all_Increasing (F:mon) :
    is_true (Increasing F) -> is_true (Fix F (H_sup bot)).
  Proof.
    intro. setoid_rewrite <- BForall_spec in H. assert (is_true (weq_mon (comp F H_sup) H_sup)).
    + apply weq_spec. split. apply (sup_spec (B_CPO := B_CPO_mon) Increasing_functions). reflexivity.
      unfold Increasing_functions. cbn. apply BForall_spec. intro x. fold_leq. transitivity (H_sup x). 
      transitivity (H_sup x). pose proof H_sup_is_increasing.
      setoid_rewrite <- BForall_spec in H0. apply H0. reflexivity. cbn.
      apply H. unfold leq_in_prop. cbn. apply BForall_spec. intro x. apply H.
    + unfold Fix. cbn in H0. rewrite <- BForall_spec in H0. apply H0.
  Qed.

  (* Lemma 8.21*)
  Lemma increasing_has_fix_point (F:mon) : is_true (Increasing F) -> exists x, is_true (Fix F x).
  Proof.
    intro. exists (H_sup bot). now apply H_sup_bot_is_fixpoint_of_all_Increasing.
  Qed.
  
  (*
  Lemma restricted_increasing_has_fix_point (F:mon) Y : is_true (Increasing_restricted Y F) 
    -> exists x, is_true (Fix F x).
  Proof.
    intro. exists (H_sup bot). apply H_sup_bot_is_fixpoint_of_all_Increasing.

Faux, il faut vraiment se restreindre à Y *)

End Increasing_fixpoint.



Section Fixpoints.
  Context {X} {B} {Bp : B_param B} {Bpp : B_param_plus X Bp} {P' : B_PO (X := X)} {P : B_CPO P'}.
  Context  {Bpp_mon : B_param_plus mon Bp} {Bpd : B_param_dir B Bp P'}.

  Definition is_least S x := is_true (S x) /\ forall y, is_true (S y) -> x <= y.
  Definition is_inf S x := forall z, (forall y, is_true (S y) -> z <= y) <-> z <= x.
  Definition is_minimal S x := is_true (S x) /\ forall y, is_true (S y) -> y <= x -> y == x.
  Definition is_greatest S x := is_true (S x) /\ forall y, is_true (S y) -> y <= x.
  Definition is_sup S x := forall z, (forall y, is_true (S y) -> y <= z) <-> x <= z.

(*
  Lemma test_coherence1 : forall (D : directed_set _), is_sup D (sup D).
  Proof. intros D z. split; apply sup_spec. Qed.
  Lemma test_coherence2 : forall (D : directed_set _),
      D (sup D) ->
      is_greatest D (sup D).
  Proof. intros. split. assumption. now apply sup_spec. Qed.
*)


  Variable F:mon.
  
  (** * Fixpoint theorems and proofs : second theorem. *)

  Lemma Induction_Rule : (exists µ0, is_least (Pre F) µ0)
                         -> exists µ, is_least (Fix F) µ /\ forall x, is_true (Pre F x) -> µ <= x.
  Proof.
    intro H. destruct H as [µ0 Hmu0].
    exists µ0. repeat split.
    + apply weq_spec. split. apply Hmu0.
      apply Hmu0. unfold Pre. apply Hbody. apply Hmu0.
    + intros. apply Hmu0. now apply fix_is_pre.
    + apply Hmu0.
  Qed.

  Lemma P0_is_in_Post : is_true (included (P0 F) (Post F)).
  Proof.
    assert (is_true (Invariant F (Post F)) /\ is_true (is_subCPO (Post F))).
    + split.
    - apply BForall_spec. setoid_rewrite <- BImpl_spec. intros x H.
      setoid_rewrite <- BExists_spec in H. setoid_rewrite <- BAnd_spec in H. destruct H as [x0 [Px0 Fx]].
      unfold Post. fold_leq. rewrite Fx. apply Hbody. apply Px0.
    - apply is_subCPO_spec. setoid_rewrite included_spec. intros D H. apply sup_spec. intros.
      transitivity (F y). now apply H. apply Hbody. now apply leq_xsup.
      + now apply P0_is_smallest_invariant_subCPO.
  Qed.
  (* Note : contrarily to the book, here P0' was never used for now, neither was phi. *)

  Lemma P0_is_in_down x : is_true (Fix F x) -> is_true (included (P0 F) (down x)).
  Proof.
    intro. assert (is_true (Invariant F (down x)) /\ is_true (is_subCPO (down x))).
    + split.
    - unfold_spec. (*apply BForall_spec. setoid_rewrite <- BImpl_spec. setoid_rewrite <- BExists_spec.*)
      intros y Hy. destruct Hy as [x0 [Dx0 Fyx0]]. unfold down. fold_leq. unfold Fix in H.
      rewrite <- H. rewrite Fyx0. apply Hbody. apply Dx0.
    - apply down_is_subCPO.
      + now apply P0_is_smallest_invariant_subCPO.
  Qed.

(* Need to change this so that I don't need dependent pair. Go back to Increasing and define it on a subset. *)
(*
  Program Instance P0_PO : B_PO (set_type (P0 F)) := (subPO _).
  Program Instance P0_CPO : CPO P0_PO := (subCPO _).
  Next Obligation. apply P0_is_invariant_subCPO. Qed.

  Program Definition F_restricted_to_P0 : mon :=
    {| body := fun y => (exist _ (F y) _) |}.
  Next Obligation. destruct y as [x Hx]; cbn. apply P0_is_invariant_subCPO. now apply from_image. Qed.
  Next Obligation. intros y1 y2 H12; cbn. now apply Hbody. Qed.
*)






(* ------ Dodging subCPOs ------ *)

 Definition mon_fun_applied (Y : X -> B) (z : X) (x0 : X) := 
  BExists_fun (fun h => BAnd (weq x0 (h z)) 
                       (BAnd (BForall (fun x => BForall (fun y => BImpl (Y x) (BImpl (Y y) (BImpl (leq x y) (leq (h x) (h y))) ))))
                       (BAnd (BForall (fun x => BImpl (Y x) (leq x (h x))))
                       (BAnd (BForall (fun x => BImpl (Y x) (Y (h x))))
                       (Y z))))).
 
 Lemma mon_fun_spec (Y : X -> B) (z : X) :
  forall x0, (exists (h : X -> X), is_true (weq x0 (h z))
                                /\ (forall x y, is_true (Y x) -> is_true (Y y) -> is_true (leq x y) -> is_true (leq (h x) (h y))) (* h monotonous *)
                                /\ (forall x, is_true (Y x) -> is_true (leq x (h x))) (* h increasing *)
                                /\ (forall x, is_true (Y x) -> is_true (Y (h x)))  (* h well defined on Y *)
                                /\ is_true (Y z))
  <-> is_true (mon_fun_applied Y z x0).
 Proof.
 unfold mon_fun_applied. unfold_spec. intuition. Qed.

 Lemma directed_set_of_fun (Y : X -> B) (z : X) : is_true (Directed leq (mon_fun_applied Y z)).
 Proof.
  rewrite <- Directed_spec. repeat setoid_rewrite <- mon_fun_spec.
  intros x y Hx Hy. destruct Hx as [hx [Hhx [hxmon [hxinc [hxinv HYx]]]]].
  destruct Hy as [hy [Hhy [hymon [hyinc [hyinv HYy]]]]].
  (*destruct Hx as [hx Hx]. destruct Hy as [hy Hy].*)
  exists (hx (hy z)). repeat split. exists (fun x => hx (hy x)).
  + (*intro HYz.*) (*destruct Hx as [Hhx [hxmon [hxinc [hxinv HYx]]]].*)(*assumption.*)
  (*destruct Hy as [Hhy [hymon [hyinc [hyinv HYy]]]].*) (*assumption.*) repeat split.
  fold_weq. reflexivity.
  intros x0 y0 Hx0 Hy0 Hxy0. apply hxmon; try now apply hyinv. now apply hymon.
  intros x0 Hx0. fold_leq. transitivity (hy x0). now apply hyinc. apply hxinc. now apply hyinv.
  intros x0 Hx0. apply hxinv. now apply hyinv. assumption.
  + fold_leq. transitivity (hx z). now rewrite <- Hhx. apply hxmon. assumption. now apply hyinv. now apply hyinc.
  + fold_leq. fold (weq_in_prop y (hy z)) in Hhy. transitivity (hy z). now rewrite <- Hhy. apply hxinc. now apply hyinv.
 Qed.


 Program Definition fun_on_Y_subCPO (Y: X -> B) z : directed_set leq := exist _ (mon_fun_applied Y z) _.
 Next Obligation. apply directed_set_of_fun. Defined.



 Lemma set_of_fun_is_subCPO (Y : X -> B) : is_true (is_subCPO Y) 
   -> (forall x y, weq_in_prop x y -> (is_true (Y x) <-> is_true (Y y))) (* WARNING : Y need to preserve weq ! *)
   -> is_true (mon_fun_applied Y bot (sup (fun_on_Y_subCPO Y bot))).
 Proof. unfold is_subCPO. setoid_rewrite <- BForall_directed_set_spec.
  unfold_spec. intro H. exists (fun x => sup (fun_on_Y_subCPO Y x)). repeat split.
  + fold_weq. reflexivity.
  + intros x y HYx HYy Hxy. apply sup_spec. cbn. setoid_rewrite <- mon_fun_spec. intros z Hz. 
    destruct Hz as [hz [Hhz [hzmon [hzinc [hzinv HYz]]]]].
    transitivity (hz y). rewrite Hhz. apply hzmon; assumption. apply leq_xsup. cbn.
    rewrite <- mon_fun_spec. exists hz. repeat split; intuition. now fold_weq.
  + intros x HYx. apply leq_xsup. cbn. rewrite <- mon_fun_spec. exists id. repeat split; intuition.
    now fold_weq. now fold_leq.
  + intros x HYx. apply H. setoid_rewrite <- mon_fun_spec. intros z Hz.
    destruct Hz as [hz [Hhz [hzmon [hzinc [hzinv HYz]]]]]. apply H0 with (hz x). apply Hhz. now apply hzinv.
  + apply H. intros x Hx. cbn in Hx. now apply BFalse_spec in Hx.
 Qed.

 Hypothesis fun_ext : forall x y, x == y -> is_true (P0 F x) <-> is_true (P0 F y). (* still need functional extensionality *)

 Theorem Fixpoint_II_no_subCPO : exists x, is_true (Fix F x).
 Proof.
 exists (sup (fun_on_Y_subCPO (P0 F) bot)). pose proof (P0_is_invariant_subCPO F fun_ext) as [PI PS].
 assert (is_true ((P0 F) (sup (fun_on_Y_subCPO (P0 F) bot)))).
 rewrite <- is_subCPO_spec in PS.
 apply PS. apply included_spec. cbn. setoid_rewrite <- mon_fun_spec.
 intros x Hx. destruct Hx as [hx [Hhx [hxmon [hxinc [hxinv HYx]]]]].
 apply fun_ext with (hx bot). apply Hhx. apply hxinv. assumption.
 
 unfold Fix. fold_weq. apply weq_spec. split.
 
 + pose proof (set_of_fun_is_subCPO (P0 F) PS fun_ext) as HP. rewrite <- mon_fun_spec in HP.
   destruct HP as [hx [Hhx [hxmon [hxinc [hxinv HYx]]]]].
   rewrite Hhx at 1. apply leq_xsup. cbn. rewrite <- mon_fun_spec. exists (fun x => F (hx x)). repeat split. 
  - fold_weq. reflexivity.
  - intros x y Hx Hy Hxy. apply Hbody. now apply hxmon.
  - intros x Hx. fold_leq. transitivity (hx x). now apply hxinc.
    pose proof P0_is_in_Post. rewrite included_spec in H0. apply H0. now apply hxinv.
  - intros x Hx. unfold Invariant in PI. rewrite included_spec in PI. apply PI. unfold Image.
    rewrite <- BExists_spec. setoid_rewrite <- BAnd_spec.
    exists (hx x). split. now apply hxinv. fold_weq. reflexivity.
  - assumption. 
 + pose proof P0_is_in_Post. rewrite included_spec in H0. apply H0.
   rewrite <- is_subCPO_spec in PS. apply PS. rewrite included_spec. cbn.
   setoid_rewrite <- mon_fun_spec. intros x Hx. 
   destruct Hx as [hx [Hhx [hxmon [hxinc [hxinv HYx]]]]].
   apply fun_ext with (hx bot). apply Hhx. now apply hxinv.
 Qed.






(*
  Lemma F_restricted_is_increasing : Increasing F_restricted_to_P0.
  Proof. intro y. destruct y as [x Hx]; cbn. now apply P0_is_in_Post. Qed.

  Theorem Fixpoint_II : exists x, Fix F x.
  Proof.
    destruct (increasing_has_fix_point F_restricted_to_P0 F_restricted_is_increasing).
    destruct x as [x Hx]. cbn in H. now exists x.
  Qed.

  (* Actually, we can go further. Since we constructively built the fixpoint of G as being (H_sup bot) for a well-chosen CPO.
 So we can define this fixpoint and add the results from Claim 3 of the theorem : it is both the top of P0 and the least fixpoint of F.*)

  Definition a := (H_sup bot). (*Here a is of type (set_type P0) since this was the last CPO to be defined.
 It's what we want, no need to specify implicit arguments. *)

  Lemma a_is_fixpoint_of_F : Fix F (element a).
  Proof.
    assert (Fix F_restricted_to_P0 a). apply H_sup_bot_is_fixpoint_of_all_Increasing. apply F_restricted_is_increasing.
    destruct a as [a Ha]. now cbn in *.
  Qed.

  Theorem a_is_top_of_P0_and_least_fixpoint_of_F :
    is_greatest (P0 F) (element a) /\ is_least (Fix F) (element a).
  Proof. split.
         + split. destruct a as [µ Hmu]. now cbn. apply P0_is_in_down.
           intros. apply a_is_fixpoint_of_F.
         + split. apply a_is_fixpoint_of_F. intros. apply (P0_is_in_down y).
           assumption. destruct a as [µ Hmu]. now cbn.
  Qed.
*)
End Fixpoints.

