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

#[global] Instance trans_Impl `{B_param} : Transitive (fun b1 b2 => is_true (BImpl b1 b2)).
Proof. intros b1 b2 b3. setoid_rewrite <- BImpl_spec. tauto. Qed.
#[global] Instance refl_Impl `{B_param} : Reflexive (fun b1 b2 => is_true (BImpl b1 b2)).
Proof. intro b1. setoid_rewrite <- BImpl_spec. tauto. Qed.

Class B_param_plus (B : Type) (X : Type) `(B_param B) := {
  BForall : (X -> B) -> B;(*Needed for Inf, for comparison of monotonous functions, and for set equality.*)
  BForall_spec : forall (P : X -> B), (forall x, is_true (P x)) <-> is_true (BForall P);
  BExists : (X -> B) -> B; (*Needed for Images of functions and monotonous complete lattice*)
  BExists_spec : forall (P : X -> B), (exists x, is_true (P x)) <-> is_true (BExists P);
  BExists_set : ((X -> B) -> B) -> B; (*needed for the Complete Lattice of parts/subsets*)
  BExists_set_spec : forall (P : (X -> B) -> B), (exists S, is_true (P S)) <-> is_true (BExists_set P);
  
  
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

End B.

Section CPO_CL.

Context {X : Type} {B} {Bp : B_param B}.  (*{Bpp : B_param_plus X Bp}.*)

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

Definition Directed (D : set) `(leq_in_prop : X -> X -> Prop) : Prop := 
  forall x y, is_true (D x) -> is_true (D y) -> exists z, is_true (D z) /\ leq_in_prop x z /\ leq_in_prop y z.
Definition directed_set `(leq_in_prop : X -> X -> Prop) := {Dbody : set | Directed Dbody leq_in_prop}.
Definition Dbody `(leq_in_prop : X -> X -> Prop) (D : directed_set leq_in_prop) : set := proj1_sig D.
Coercion Dbody : directed_set >-> Funclass.

Class B_CPO `(P' : B_PO) := {
    sup: directed_set leq_in_prop -> X;
    sup_spec: forall D z, (leq_in_prop (sup D) z <-> forall (y:X), is_true ((Dbody D) y) -> leq_in_prop y z);
  }.

(* Definition of Lattice as a particular (stronger) CPO. *)
Class B_CL `(L' : B_PO) := {
    Sup: (X -> B) -> X;
    (*sup_spec0 : forall Y y, is_true (Y y) -> is_true (leq y (sup Y));*)
    Sup_spec: forall Y z, leq_in_prop (Sup Y) z <-> (forall y, is_true (Y y) -> leq_in_prop y z);
  }.
  (* Convention : capital letters for CL from now on. *)

End CPO_CL.

Declare Scope B_PO.
Open Scope B_PO.
Infix "==" := weq_in_prop (at level 70): B_PO.
Infix "<=" := leq_in_prop (at level 70): B_PO.
#[global] Hint Extern 0 => reflexivity: core.



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

End Partial_order.



Section sup.

  Context {X} {B} {Bp : B_param B} {P' : B_PO (X := X)} {P : B_CPO P'} {L : B_CL P'}.
  Context {Bpp : B_param_plus X Bp}.

  Lemma leq_xsup (D: directed_set leq_in_prop) (y : X) : is_true (D y) -> y <= sup D.
  Proof. intro H. now apply (sup_spec D). Qed.
  Lemma leq_xSup (Y: X -> B) (y : X) : is_true (Y y) -> y <= Sup Y.
  Proof. intro H. now apply (Sup_spec Y). Qed.

  Program Definition empty : directed_set leq_in_prop :=
    exist _ (fun _ => BFalse) _.
  Next Obligation. unfold Directed. intros. contradict H. apply BFalse_spec. Defined.

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

  Context {X} {B} {Bp : B_param B} {P' : B_PO (X := X)} {P : B_CPO P'}.
  Context {Bpp : B_param_plus X Bp}.

  Definition Fix F x := F x == x.
  Definition Post F x := x <= F x.
  Definition Pre F x := F x <= x.

  Lemma fix_is_post F : forall x, Fix F x -> Post F x.
  Proof. intros. apply weq_spec in H. apply H. Qed.
  Lemma fix_is_pre F : forall x, Fix F x -> Pre F x.
  Proof. intros. apply weq_spec in H. apply H. Qed.

  #[global] Instance Hbody' (F:mon) : Proper (weq_in_prop ==> weq_in_prop) F.
  Proof. intros x y Hxy. apply weq_spec. split; apply Hbody; now apply weq_spec in Hxy. Qed.

  Definition Image f (S : X -> B) y := (BExists (fun x => BAnd (S x) (weq y (f x)))).

  Definition Continuous f :=
    forall (D : X -> B) (H : Directed D leq_in_prop),
      {dir_im : Directed (Image f D) leq_in_prop &
                f (sup (exist _ D H )) == sup (exist _ (Image f D) dir_im)}.

  Lemma mon_preserves_directedness_and_sup (F:mon) :
    forall (D : X -> B) (H : Directed D leq_in_prop),
      {dir_im : Directed (Image F D) leq_in_prop &
                  sup (exist _ (Image F D) dir_im) <= F (sup (exist _ D H ))}.
  Proof.
    intros. assert (Directed (Image F D) leq_in_prop) as DD.
    + unfold Directed. intros y1 y2 Hfy1 Hfy2. apply BExists_spec in Hfy1, Hfy2. 
      destruct Hfy1 as [x1 Hx1]. destruct Hfy2 as [x2 Hx2].
      apply BAnd_spec in Hx1, Hx2. destruct Hx1 as [Dx1 Hx1]. destruct Hx2 as [Dx2 Hx2].
      destruct (H x1 x2) as [x Hx]; try assumption.
      exists (F x). repeat split. apply BExists_spec. exists x. apply BAnd_spec. split.
      apply Hx. fold (weq_in_prop (F x) (F x)). reflexivity. rewrite Hx1.
      now apply Hbody. rewrite Hx2. now apply Hbody.
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

  Lemma itere_preserves_fix (F:mon) : forall β n, Fix F β -> (itere F n β) == β.
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
  
  Definition included_prop (S T : X -> B) := is_true (included S T).
  
End Sets.
Infix "⊆" := included_prop (at level 70).




Section Particular_CPOs.

  Context {X} {B} {Bp : B_param B} {P' : B_PO (X := X)} {P : B_CPO P'}.
  Context {Bpp : B_param_plus X Bp} {Bpp_mon : B_param_plus mon Bp}.

 Program Instance B_PO_mon : @B_PO mon B Bp :=
    {|
      weq f g := BForall (fun (x:X) => weq (f x) (g x));
      leq f g := BForall (fun (x:X) => leq (f x) (g x));
    |}.
  Next Obligation.
  apply Build_PreOrder.
    + intro x. apply BForall_spec. intro. fold (leq_in_prop (x x0) (x x0)). reflexivity.
    + intros f g h Hfg Hgh. apply BForall_spec. intro x. fold (leq_in_prop (f x) (h x)).
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
      sup (F : @directed_set mon B Bp leq_in_prop) := {| body x := sup (fun y => BExists (*B mon Bp Bpp_mon*) (fun f => BAnd (F f) (weq y (f x)))) |};
    |}.
  Next Obligation.
    unfold Directed. setoid_rewrite <- BExists_spec.
    intros. destruct F as [SF D]; cbn in *.
    destruct H as [fx Hfx]. destruct H0 as [fy Hfy]. rewrite <- BAnd_spec in Hfx, Hfy.
    destruct Hfx as [Hfx Eqfx]. destruct Hfy as [Hfy Eqfy].
    destruct (D fx fy) as [f [Hf1S [Hff1 Hff2]]]; try assumption.
    exists (f x). unfold leq_in_prop in Hff1, Hff2. cbn in *. rewrite <- BForall_spec in Hff1, Hff2.
    repeat split. exists f. apply BAnd_spec. split. 
    assumption. fold (weq_in_prop (f x) (f x)). reflexivity.
                                 + rewrite Eqfx. apply (Hff1 x).
                                 + rewrite Eqfy. apply (Hff2 x).
  Qed.
  Next Obligation.
    destruct F as [SF D]; cbn in *.
    intros x y H. apply sup_spec; cbn. intros.
    rewrite <- BExists_spec in H0. setoid_rewrite <- BAnd_spec in H0.
    destruct H0 as [f [Hfx0 Eqyx]].
    transitivity (f y). rewrite Eqyx. now apply Hbody.
    apply leq_xsup. cbn. apply BExists_spec. exists f. apply BAnd_spec.
    split. assumption. fold (weq_in_prop (f y) (f y)). reflexivity.
  Qed.
  Next Obligation.
    destruct D as [SF D]; cbn in *. split.
    + intros H f Df. unfold leq_in_prop in *. cbn in *. rewrite <- BForall_spec in *. intro x.
      fold (leq_in_prop (f x) (z x)). rewrite <- H.
      eapply sup_spec. reflexivity. cbn. apply BExists_spec. exists f. apply BAnd_spec. split. assumption.
      now fold (weq_in_prop (f x) (f x)).
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

  Program Instance B_CPO_parts: B_CPO B_PO_parts :=
    {|
      sup A := (fun x => BExists_set (fun Y => BAnd (A Y) (Y x)));
    |}.
  Next Obligation.
    unfold leq_in_prop; cbn. split; intros. 
    + apply BForall_spec. intro x. apply BImpl_spec. intro Hx.
      setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BImpl_spec in H. 
      setoid_rewrite <- BExists_set_spec in H. apply (H x). exists y. apply BAnd_spec. now split.
    + apply BForall_spec. intro x. apply BImpl_spec. intro PDx. 
      rewrite <- BExists_set_spec in PDx. setoid_rewrite <- BAnd_spec in PDx. destruct PDx as [S [Ds Sx]].
      specialize H with S. apply H in Ds. setoid_rewrite <- BForall_spec in Ds. setoid_rewrite <- BImpl_spec in Ds.
      now apply Ds.
  Qed.

  Program Instance Lattice_parts : B_CL (B_PO_parts) :=
    {|
      Sup A := (fun x => BExists_set (fun Y => BAnd (A Y) (Y x)));
    |}.
  Next Obligation.
   unfold leq_in_prop; cbn. split; intros. 
    + apply BForall_spec. intro x. apply BImpl_spec. intro Hx.
      setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BImpl_spec in H. 
      setoid_rewrite <- BExists_set_spec in H. apply (H x). exists y. apply BAnd_spec. now split.
    + apply BForall_spec. intro x. apply BImpl_spec. intro PDx. 
      rewrite <- BExists_set_spec in PDx. setoid_rewrite <- BAnd_spec in PDx. destruct PDx as [S [Ds Sx]].
      specialize H with S. apply H in Ds. setoid_rewrite <- BForall_spec in Ds. setoid_rewrite <- BImpl_spec in Ds.
      now apply Ds.
   Qed.

End Particular_CPOs.




