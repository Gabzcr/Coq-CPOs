From Coq Require Import Arith.
Require Import Psatz.
Require Export Setoid Morphisms.
Set Implicit Arguments.

Section B.

Class B_param := { B : Type;
  K : Type -> Type;
  
  (* Basic operations on B *)
  is_true : B -> Prop;
  
  BFalse : B;
  BTrue : B;
  BFalse_spec : ~ (is_true BFalse);
  BTrue_spec : is_true BTrue;
  BAnd : B -> B -> B;
  BOr : B -> B -> B;
  BAnd_spec : forall b1 b2, is_true b1 /\ is_true b2 <-> is_true (BAnd b1 b2);
  BOr_spec : forall b1 b2, is_true b1 \/ is_true b2 <-> is_true (BOr b1 b2);
  BImpl : B -> B -> B;
  BImpl_spec : forall b1 b2, (is_true b1 -> is_true b2) <-> (is_true (BImpl b1 b2));
  
  (* Closure properties on K *)
  subtype_closure (A : Type) : K A -> forall (P : A -> B), K {a : A | is_true (P a)}; (* for Forall on directed sets*)
  function_closure (A B : Type) : K A -> K B -> K (A -> B);
  set_closure (A : Type) : K A -> K (A -> B);

  (* Forall and Exists :*)
  valid_type := { TBody : Type & K TBody};
  TBody (V : valid_type) := projT1 V;
  
  BForall (V : valid_type) : (((TBody V) -> B) -> B);
  BForall_spec (V : valid_type) : forall (P : (TBody V) -> B), 
    (forall x, is_true (P x)) <-> is_true (BForall V P);
  BExists (V : valid_type) : (((TBody V) -> B) -> B);
  BExists_spec (V : valid_type) : forall (P : (TBody V) -> B), 
    (exists x, is_true (P x)) <-> is_true (BExists V P);
  
  
  (* Memoisation for computation speed-up*)
  memo (X : valid_type) : ((projT1 X) -> B) -> ((projT1 X) -> B);
  memo_spec (X : valid_type) : forall P x, is_true (memo X P x) <-> is_true (P x);
  }.
  
  Coercion B : B_param >-> Sortclass.
  Coercion TBody : valid_type >-> Sortclass.

Definition BEq `{B_param} PB1 PB2 := BAnd (BImpl PB1 PB2) (BImpl PB2 PB1).
Lemma BEq_spec `{B_param} : forall b1 b2, (is_true b1 <-> is_true b2) <-> is_true (BEq b1 b2).
Proof. intros b1 b2. setoid_rewrite <- BAnd_spec. setoid_rewrite <- BImpl_spec. tauto. Qed.

Definition BEq_in_prop `{B_param} PB1 PB2 := is_true (BEq PB1 PB2).

#[global] Instance trans_Impl `{B_param} : Transitive (fun b1 b2 => is_true (BImpl b1 b2)).
Proof. intros b1 b2 b3. setoid_rewrite <- BImpl_spec. tauto. Qed.
#[global] Instance refl_Impl `{B_param} : Reflexive (fun b1 b2 => is_true (BImpl b1 b2)).
Proof. intro b1. setoid_rewrite <- BImpl_spec. tauto. Qed.

End B.

Ltac unfold_spec := try repeat (setoid_rewrite <- BAnd_spec)
                            || (setoid_rewrite <- BOr_spec)
                            || (setoid_rewrite <- BImpl_spec)
                            || (setoid_rewrite <- BForall_spec)
                            || (setoid_rewrite <- BExists_spec).


Section CPO_CL.

Context {B : B_param} {X : valid_type}.

Notation set := (X -> B).
Notation rel := (X -> X -> B).

Class B_PO := {
    weq: X -> X -> B;
    leq: X -> X -> B;
    weq_in_prop x y := is_true (weq x y);
    leq_in_prop x y := is_true (leq x y);
    Preorder_leq_in_prop :> PreOrder leq_in_prop;
    weq_spec: forall x y, weq_in_prop x y <-> leq_in_prop x y /\ leq_in_prop y x;
  }.


Definition Directed (leq : X -> X -> B) (D : set) : B := 
  BForall X (fun x => BForall X (fun y => BImpl (D x) (BImpl (D y) 
    (BExists X (fun z => BAnd (D z) (BAnd (leq x z) (leq y z))))))).
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
    Sup_spec: forall Y z, leq_in_prop (Sup Y) z <-> (forall y, is_true (Y y) -> leq_in_prop y z);
  }.
  (* Convention : capital letters for CL from now on. *)

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


Section Forall_sets.

 Context {B : B_param} {X : valid_type} {P' : @B_PO B X}.
  
  #[global]
  Program Definition valid_fun_type := existT K (X -> X) _.
  Next Obligation. destruct X as [T KT]; cbn. now apply function_closure. Defined.
  
  #[global]
  Program Definition valid_set_type := existT K (X -> B) _.
  Next Obligation. destruct X as [T KT]; cbn. now apply set_closure. Defined.
 
 #[global]
  Program Definition valid_dir_set_type := existT K (directed_set leq) _.
  Next Obligation. destruct X as [T KT]; cbn. apply subtype_closure. cbn.
  now apply set_closure. Defined.

End Forall_sets.


Section Partial_order.

  Context {B : B_param} {X : valid_type} {P' : @B_PO B X}.

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
  
 Definition BMonotony F := BForall X (fun x => BForall X (fun y => BImpl (leq x y) (leq (F x) (F y)))).
 Definition Monotony F := Proper (leq_in_prop ==> leq_in_prop) F.
 Lemma BMonotony_spec : forall F, Monotony F <-> (is_true (BMonotony F)).
 Proof. unfold BMonotony. unfold_spec. tauto. Qed.
  
  Definition mon := { FBody: X -> X | is_true (BMonotony FBody)}.
  Definition FBody (F : mon) : X -> X := proj1_sig F.
  Coercion FBody : mon >-> Funclass.
  
  Program Definition const x: mon := exist (fun F => is_true (BMonotony F)) (fun y => x) _.
  Next Obligation. rewrite <- BMonotony_spec. intros ? ? ?. reflexivity. Qed.

  Program Definition id: mon := exist (fun F => is_true (BMonotony F)) (fun z => z) _.
  Next Obligation. rewrite <- BMonotony_spec. intros ? ? ?. assumption. Qed.

  Program Definition comp (f g: mon): mon := exist (fun F => is_true (BMonotony F)) (fun x => f (g x)) _.
  Next Obligation. rewrite <- BMonotony_spec. intros ? ? ?. 
    destruct f as [f fmon]. destruct g as [g gmon]. cbn. rewrite <- BMonotony_spec in fmon, gmon.
  apply fmon. now apply gmon. Qed.

 Lemma from_above x y: (forall z, x<=z <-> y<=z) -> x==y.
  Proof. intro E. apply weq_spec. split; apply E; reflexivity. Qed.

  Lemma from_below x y: (forall z, z<=x <-> z<=y) -> x==y.
  Proof. intro E. apply weq_spec. split; apply E; reflexivity. Qed.

End Partial_order.
Infix "??" := comp (at level 20): B_PO.


Section Sup.

  Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {P : B_CPO P'} {L : B_CL P'}.

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

  Definition Inf (Y : X -> B) := Sup (fun z => BForall X (fun y => BImpl (Y y) (leq z y))).
  Lemma Inf_spec : forall Y z, z <= Inf Y <-> (forall y, is_true (Y y) -> z <= y).
  Proof.
    intros. split.
    intros H y Yy. rewrite H. apply Sup_spec. intros y0 H0.
    rewrite <- BForall_spec in H0. setoid_rewrite <- BImpl_spec in H0. now apply (H0 y).
    intro. apply leq_xSup. apply -> BForall_spec. intro y. apply -> BImpl_spec. intro. now apply H.
  Qed.

  Lemma leq_xInf (D: X -> B) y:  is_true (D y) -> Inf D <= y.
  Proof. intro H. now apply Inf_spec with D. Qed.

End Sup.

#[global] Hint Resolve bot_spec: core.
#[global] Hint Resolve Bot_spec: core.



Section ForLattices.

 Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {L : B_CL P'}.

(** define binary join out of arbitrary joins  *)
 Definition cup x y := Sup (fun i => BOr (weq i x) (weq i y)).
 Lemma cup_spec: forall x y z, (cup x y) <= z <-> (x <= z /\ y <= z).
Proof.
  split.
  + unfold cup. intro H. split; eapply Sup_spec; try apply H; apply BOr_spec; [left | right];
    now apply weq_spec.
  + unfold cup. intro H. apply Sup_spec. intro i. intro.
    rewrite <- BOr_spec in H0. destruct H0; rewrite H0; apply H.
Qed.

 (** define binary meet out of arbitrary joins  *)
 Definition cap x y := Sup (fun z => BAnd (leq z x) (leq z y)). (*take sup of all elements smaller than x and y*)
 Lemma cap_spec: forall x y z, z <= (cap x y) <-> (z <= x /\ z <= y).
Proof.
  intros x y z. split.
    + intro H. assert (cap x y <= x /\ cap x y <= y) as H0.
      - split; apply Sup_spec; intros i Q; rewrite <- BAnd_spec in Q; destruct Q as [H0 H1]; [apply H0|apply H1].
      - split;  destruct H0 as [H1 H2]; transitivity (cap x y). apply H. apply H1. apply H. apply H2.
    + intro H. unfold cap. apply leq_xSup. apply BAnd_spec. apply H.
Qed.

(** Binary join *)
 Lemma leq_xcup x y z: z <= x \/ z <= y -> z <= cup x y.
 Proof.
   destruct (cup_spec x y (cup x y)) as [H _].
   now intros [E|E]; rewrite E; apply H.
 Qed.
 Lemma cup_l x y: x <= cup x y.
 Proof. auto using leq_xcup. Qed.
 Lemma cup_r x y: y <= cup x y.
 Proof. auto using leq_xcup. Qed.

 Lemma cupA x y z: cup x (cup y z) == cup (cup x y) z.
 Proof. apply from_above.
  intro z0. split.
    + intro H. apply Sup_spec. unfold_spec. intros i Q. destruct Q. 
      - rewrite H0. apply Sup_spec. unfold_spec. intros i0 Q. destruct Q;
        rewrite H1; transitivity (cup x (cup y z)). apply cup_l. apply H.
        * transitivity (cup y z). apply cup_l. apply cup_r.
        * apply H.
      - rewrite H0. transitivity (cup x (cup y z)).
        * transitivity (cup y z); apply cup_r.
        * apply H.
    + intro H. apply Sup_spec. unfold_spec. intros i Q. destruct Q. 
      - rewrite H0. transitivity (cup (cup x y) z).
        * transitivity (cup x y); apply cup_l.
        * apply H.
      - rewrite H0. apply Sup_spec. unfold_spec. intros i0 Q. destruct Q;
        rewrite H1; transitivity (cup (cup x y) z). transitivity (cup x y). apply cup_r. apply cup_l. apply H.
        * apply cup_r.
        * apply H.
Qed.



 Lemma cupC x y: cup x y == cup y x.
  rewrite weq_spec. split; apply Sup_spec; intros i H; rewrite <- BOr_spec in H. (*much simpler, and exactly twice the same*)
    + destruct H as [H0|H1]; [rewrite H0|rewrite H1]; [apply cup_r | apply cup_l].
    + destruct H as [H0|H1]; [rewrite H0|rewrite H1]; [apply cup_r | apply cup_l].
  Qed.

 Lemma cupI x: cup x x == x.
 Proof.
  rewrite weq_spec. split. 
    + apply Sup_spec. intros i H. rewrite <- BOr_spec in H. destruct H; rewrite H; reflexivity.
    + apply cup_l.
Qed.

End ForLattices.

Global Hint Resolve cup_l cup_r: core.





(* Knaster-Tarski Theorem on Lattices *)

Section Knaster_Tarski.
  Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {L : B_CL P'}.
  Variable b: mon.

  Definition gfp := Sup (fun x => leq x (b x)).
  Definition lfp := Inf (fun x => leq (b x) x).

  Proposition leq_gfp: forall y, y <= b y -> y <= gfp.
  Proof. apply leq_xSup. Qed.
  Proposition geq_lfp: forall y, b y <= y -> lfp <= y.
  Proof. apply leq_xInf. Qed.

  Lemma gfp_pfp: gfp <= b gfp.
  Proof.
    unfold gfp. apply Sup_spec. intros y H. rewrite H. destruct b as [bf bmon]. cbn in *.
    rewrite <- BMonotony_spec in bmon. apply bmon. apply leq_xSup. apply H.
  Qed.
  Lemma lfp_pfp: b lfp <= lfp.
  Proof.
    unfold lfp. apply Inf_spec. intros y H. rewrite <- H. destruct b as [bf bmon]. cbn in *.
    rewrite <- BMonotony_spec in bmon. apply bmon. apply leq_xInf. apply H.
  Qed.

  Lemma gfp_fp: gfp == b gfp.
  Proof.
    rewrite weq_spec. split.
    + apply gfp_pfp.
    + apply leq_xSup. pose proof gfp_pfp. destruct b as [bf bmon]. cbn in *.
      rewrite <- BMonotony_spec in bmon. now apply bmon.
  Qed.
  Lemma lfp_fp: lfp == b lfp.
  Proof.
    rewrite weq_spec. split.
    + apply leq_xInf. pose proof lfp_pfp. destruct b as [bf bmon]. cbn in *.
      rewrite <- BMonotony_spec in bmon. now apply bmon.
    + apply lfp_pfp.
  Qed.

End Knaster_Tarski.



Section Function.

  Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {P : B_CPO P'}.

  Definition Fix F x := weq (F x) x.
  Definition Post F x := leq x (F x).
  Definition Pre F x := leq (F x) x.

  Lemma fix_is_post F : forall x, is_true (Fix F x) -> is_true (Post F x).
  Proof. intros. apply weq_spec in H. apply H. Qed.
  Lemma fix_is_pre F : forall x, is_true (Fix F x) -> is_true (Pre F x).
  Proof. intros. apply weq_spec in H. apply H. Qed.

  #[global] Instance Hbody' (F:mon) : Proper (weq_in_prop ==> weq_in_prop) F.
  Proof. intros x y Hxy. apply weq_spec. destruct F as [F Fmon]. cbn. 
  rewrite <- BMonotony_spec in Fmon.
  split; apply Fmon; now apply weq_spec in Hxy. Qed.

  Definition Image f (S : X -> B) y := (BExists X (fun x => BAnd (S x) (weq y (f x)))).
  Lemma Image_spec f S y : (exists x, is_true (S x) /\ y == (f x)) <-> is_true (Image f S y).
  Proof. unfold_spec. tauto. Qed.

  Definition Continuous f :=
    forall (D : X -> B) (H : is_true (Directed leq D)),
      {dir_im : is_true (Directed leq (Image f D)) &
                f (sup (exist _ D H )) == sup (exist _ (Image f D) dir_im)}.

  Lemma mon_preserves_directedness_and_sup (F:mon) :
    forall (D : X -> B) (H : is_true (Directed leq D)),
      {dir_im : is_true (Directed leq (Image F D)) &
                  sup (exist _ (Image F D) dir_im) <= F (sup (exist _ D H ))}.
  Proof.
    intros. destruct F as [F Fmon]. cbn. rewrite <- BMonotony_spec in Fmon.
    assert (is_true (Directed leq (Image F D))) as DD.
    + apply Directed_spec. intros y1 y2 Hfy1 Hfy2. apply BExists_spec in Hfy1, Hfy2. 
      destruct Hfy1 as [x1 Hx1]. destruct Hfy2 as [x2 Hx2].
      apply BAnd_spec in Hx1, Hx2. destruct Hx1 as [Dx1 Hx1]. destruct Hx2 as [Dx2 Hx2].
      rewrite <- Directed_spec in H.
      destruct (H x1 x2) as [x Hx]; try assumption.
      exists (F x). repeat split. apply BExists_spec. exists x. apply BAnd_spec. split.
      apply Hx. fold_weq. reflexivity. fold_leq. fold (weq_in_prop y1 (F x1)) in Hx1.
      apply weq_spec in Hx1. destruct Hx1 as [Hx1 _]. transitivity (F x1).
      apply Hx1. apply Fmon. apply Hx. fold (weq_in_prop y2 (F x2)) in Hx2. fold_leq.
      transitivity (F x2). now apply weq_spec in Hx2. now apply Fmon.
    + exists DD. apply sup_spec; cbn. intros y Hy.
      apply BExists_spec in Hy. destruct Hy as [x Hx]. apply BAnd_spec in Hx. destruct Hx as [Dx Hx].
      rewrite Hx. apply Fmon. now apply leq_xsup.
  Qed.


  Fixpoint itere F n x0 : X :=
    match n with
    | 0 => x0
    | S m => F (itere F m x0)
    end. (*Indexed by n for simplicity on comparison properties.*)

  Lemma itere_monotony (F:mon) : forall n, Proper (leq_in_prop ==> leq_in_prop) (itere F n).
  Proof. intros n x y H. induction n. now cbn. cbn. destruct F as [F Fmon]. cbn in *.
    rewrite <- BMonotony_spec in Fmon. now apply Fmon. Qed.

  Lemma chain_itere (F:mon) : forall (n : nat), itere F n bot <= itere F (S n) bot.
  Proof. intro n. induction n. now cbn. cbn. destruct F as [F Fmon]. cbn in *.
    rewrite <- BMonotony_spec in Fmon. now apply Fmon. Qed.

  Lemma chain_increase (F:mon) : forall (m n : nat), le n m -> itere F n bot <= itere F m bot.
  Proof.
    intros m n H. induction m. now inversion H.
    inversion H. easy.
    rewrite <- chain_itere. now apply IHm.
  Qed.

  Lemma itere_preserves_fix (F:mon) : forall ?? n, is_true (Fix F ??) -> (itere F n ??) == ??.
  Proof.
    intros. induction n. now cbn. cbn. unfold Fix in H. rewrite <- H at 2.
    now apply Hbody'.
  Qed.

End Function.



(** * Sets general properties *)

Section Sets.

  Context {B : B_param} {X : valid_type} {P' : @B_PO B X}.

  Definition set_eq (f g : X -> B) :=  BForall X (fun z => (BEq (f z) (g z))). (*equality of sets*)

  Definition included (S T: X -> B) := BForall X (fun x => (BImpl (S x) (T x))).
  Lemma included_spec (S T : X -> B) : is_true (included S T) <-> forall x, is_true (S x) -> is_true (T x).
  Proof. setoid_rewrite <- BForall_spec. now setoid_rewrite <- BImpl_spec. Qed.
  
  Definition included_prop (S T : X -> B) := is_true (included S T).
  
End Sets.
Infix "???" := included_prop (at level 70).




Section Particular_CPOs.

 Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {P : B_CPO P'}.

 (** * CPO of monotonous functions in X -> X. *)
 
 #[global]
  Program Definition valid_mon_type := existT K (mon) _.
  Next Obligation. destruct X as [T KT]; cbn. unfold mon. apply subtype_closure. now apply function_closure. Qed.

(* PB : J'ai d??fini les CPO sur les types valides, car j'avais besoin d'un forall sur X pour d??finir les ensembles dirig??s.
Donc il faut que l'ensemble des fonctions monotones soit aussi un type valide. Ceci requiert functional extentisionality (cf FiniteSet.v) . *)

 Program Instance B_PO_mon : @B_PO B valid_mon_type :=
    {|
      weq f g := BForall X (fun (x:X) => weq (f x) (g x));
      leq f g := BForall X (fun (x:X) => leq (f x) (g x));
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


 Program Definition dir_F_dir (F: @directed_set B valid_mon_type leq) (x : X) := exist (Directed_in_prop leq)
  (fun y => BExists (valid_mon_type) (fun (f : mon) => BAnd (F f) (weq y (f x)))) _.
 Next Obligation. 
  apply Directed_spec. repeat setoid_rewrite <- BExists_spec.
    intros. destruct F as [SF D]; cbn in *. setoid_rewrite <- Directed_spec in D.
    destruct H as [fx Hfx]. destruct H0 as [fy Hfy]. rewrite <- BAnd_spec in Hfx, Hfy.
    destruct Hfx as [Hfx Eqfx]. destruct Hfy as [Hfy Eqfy].
    destruct (D fx fy) as [f [Hf1S [Hff1 Hff2]]]; try assumption. unfold valid_mon_type in f. destruct f as [f fmon]. cbn in *.
    exists (f x). unfold leq_in_prop in Hff1, Hff2. cbn in *. rewrite <- BForall_spec in Hff1, Hff2.
    repeat split. exists (exist _ f fmon). apply BAnd_spec. split. 
    assumption. fold_weq. reflexivity.
                                 + fold (leq_in_prop x0 (f x)). transitivity (fx x).
                                   apply weq_spec in Eqfx. apply Eqfx. apply (Hff1 x).
                                 + fold (leq_in_prop y (f x)). transitivity (fy x).
                                   apply weq_spec in Eqfy. apply Eqfy. apply (Hff2 x).
  Qed.

 Lemma mon_F_dir (F: @directed_set B valid_mon_type leq) : 
  is_true (BMonotony (fun (x : X) => sup (dir_F_dir F x))).
 Proof.
    destruct F as [SF D]; cbn in *. rewrite <- BMonotony_spec.
    intros x y H. apply sup_spec; cbn. intros.
    rewrite <- BExists_spec in H0. setoid_rewrite <- BAnd_spec in H0.
    destruct H0 as [f [Hfx0 Eqyx]]. destruct f as [f fmon]. cbn in *.
    transitivity (f y). rewrite Eqyx. clear Hfx0. rewrite <- BMonotony_spec in fmon. now apply fmon.
    apply leq_xsup. cbn. apply BExists_spec. exists (exist _ f fmon). apply BAnd_spec.
    split. assumption. fold_weq. reflexivity.
  Qed.
  
  Program Definition F_dir_fun (F : @directed_set B valid_mon_type leq) := 
    exist (fun f => is_true (BMonotony f)) (fun x => sup (dir_F_dir F x)) _.
  Next Obligation. apply mon_F_dir. Qed.

  Program Instance B_CPO_mon : B_CPO B_PO_mon :=
    {|
      sup F := F_dir_fun F;
      (*sup (F : @directed_set mon B leq) := {| body x := 
        sup (fun y => BExists (*B mon Bp Bpp_mon*) (fun f => BAnd (F f) (weq y (f x)))) |};*)
    |}.
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

  Program Instance B_PO_parts: @B_PO B (@valid_set_type B X P') :=
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
      sup A := (fun x => BExists (valid_set_type) (fun Y => BAnd (A Y) (Y x)));
    |}.
  Next Obligation.
    unfold leq_in_prop; cbn. split; intros. 
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro Hx.
      setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BImpl_spec in H.
      setoid_rewrite <- BExists_spec in H. apply (H x). exists y. apply BAnd_spec. now split.
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro PDx. 
      rewrite <- BExists_spec in PDx. setoid_rewrite <- BAnd_spec in PDx. destruct PDx as [S [Ds Sx]].
      specialize H with S. apply H in Ds. setoid_rewrite <- BForall_spec in Ds. setoid_rewrite <- BImpl_spec in Ds.
      now apply Ds.
  Qed.

  Program Instance Lattice_parts : B_CL (B_PO_parts) :=
    {|
      Sup A := (fun x => BExists (valid_set_type) (fun Y => BAnd (A Y) (Y x)));
    |}.
+++++++++++  Next Obligation.
   unfold leq_in_prop; cbn. split; intros. 
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro Hx.
      setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BImpl_spec in H. 
      setoid_rewrite <- BExists_spec in H. apply (H x). exists y. apply BAnd_spec. now split.
    + unfold included. rewrite <- BForall_spec. intro x. apply BImpl_spec. intro PDx. 
      rewrite <- BExists_spec in PDx. setoid_rewrite <- BAnd_spec in PDx. destruct PDx as [S [Ds Sx]].
      specialize H with S. apply H in Ds. setoid_rewrite <- BForall_spec in Ds. setoid_rewrite <- BImpl_spec in Ds.
      now apply Ds.
   Qed.


(** * sub-CPO : Define a set (part of X) as being a CPO *)

  Definition is_subCPO (Y : X -> B) :=   
    BForall (valid_dir_set_type) (fun D => (BImpl (included (Dbody D) Y) (Y (sup D)))).
  Lemma is_subCPO_spec Y : (forall (D : directed_set _),
      is_true (included D Y) -> is_true (Y (sup D))) <-> is_true (is_subCPO Y).
  Proof.
    setoid_rewrite <- BForall_spec. repeat setoid_rewrite <- BImpl_spec. 
    setoid_rewrite included_spec. tauto.
  Qed.

  Definition down (x:X) := (fun z => leq z x).

  Lemma down_is_subCPO : forall x, is_true (is_subCPO (down x)).
  Proof. setoid_rewrite <- is_subCPO_spec. intros x D Hd. unfold down. apply sup_spec.
   intros. rewrite included_spec in Hd. now apply Hd. Qed.


  (* Some instances that can now be defined on CPO_parts and CPO_mon. *)

   Lemma set_equivalent : forall (f g : X -> B), f == g -> (pointwise_relation X BEq_in_prop) f g.
  Proof.
    intros f g H x. apply BEq_spec. apply weq_spec in H.
    unfold leq_in_prop in *; cbn in *. setoid_rewrite included_spec in H. intuition.
  Qed.

  Variable F : X -> X.

  #[global] Instance set_incl : Proper (@weq_in_prop B valid_set_type B_PO_parts ==> weq_in_prop ==> BEq_in_prop) included.
  Proof. intros Y1 Y2 H12 Y3 Y4 H34. apply BEq_spec. setoid_rewrite included_spec.
   apply weq_spec in H12, H34. destruct H12 as [H12 H21]. destruct H34 as [H34 H43].
   unfold leq_in_prop in *; cbn in *. rewrite included_spec in H12, H21, H34, H43. intuition.
  Qed.


(** * More generally, CPO A -> X when A is a valid type and X is a CPO *)

#[global]
  Program Definition valid_gfun_type {A : valid_type} := existT K (A->X) _.
  Next Obligation. destruct X as [TX KTX]; cbn. destruct A as [TA KTA]; cbn.
    now apply function_closure. Defined.


 Program Instance B_PO_fun `{A : valid_type} : @B_PO B (@valid_gfun_type A) :=
    {|
      weq f g := BForall A (fun (x:A) => weq (f x) (g x));
      leq f g := BForall A (fun (x:A) => leq (f x) (g x));
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
  
Program Instance B_CPO_fun {A : valid_type} : B_CPO (@B_PO_fun A) :=
  {|
    sup G := fun x => sup (fun y => BExists (@valid_gfun_type A) (fun f => BAnd (G f) (weq y (f x))));
  |}.
  Next Obligation.
  apply Directed_spec. repeat setoid_rewrite <- BExists_spec.
    intros. destruct G as [SF D]; cbn in *. setoid_rewrite <- Directed_spec in D.
    destruct H as [fx Hfx]. destruct H0 as [fy Hfy]. rewrite <- BAnd_spec in Hfx, Hfy.
    destruct Hfx as [Hfx Eqfx]. destruct Hfy as [Hfy Eqfy].
    destruct (D fx fy) as [f [Hf1S [Hff1 Hff2]]]; try assumption. unfold valid_gfun_type in f. cbn in *.
    exists (f x). unfold leq_in_prop in Hff1, Hff2. cbn in *. rewrite <- BForall_spec in Hff1, Hff2.
    repeat split. exists f. apply BAnd_spec. split. 
    assumption. fold_weq. reflexivity.
                                 + fold (leq_in_prop x0 (f x)). transitivity (fx x).
                                   apply weq_spec in Eqfx. apply Eqfx. apply (Hff1 x).
                                 + fold (leq_in_prop y (f x)). transitivity (fy x).
                                   apply weq_spec in Eqfy. apply Eqfy. apply (Hff2 x).
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


End Particular_CPOs.


(** * Invariant subCPOs *)

Section Invariant_subCPOs.

  Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {P : B_CPO P'}.

  Definition Invariant (F : X -> X) Y := included (Image F Y) Y.

  Variable F : X -> X.

  Definition P0 x :=  (*P0 is the smallest invariant subCPO : intersection of all invariant sub_CPOs.*)
    BForall (valid_set_type) (fun Y => BImpl (Invariant F Y) (BImpl (is_subCPO Y) (BImpl 
      (BForall X (fun x => BForall X (fun y => BImpl (weq x y) (BEq (Y x) (Y y))))) 
      (Y x)))).
  
  Lemma P0_spec : forall x, (forall Y, is_true (Invariant F Y) -> is_true (is_subCPO Y) 
    -> (forall x y, x == y -> is_true (Y x) <-> is_true (Y y))
    -> is_true (Y x)) <-> is_true (P0 x).
  Proof. unfold_spec. tauto. Qed.
  
  Lemma P0_preserves_weq : forall x y, x == y -> is_true (P0 x) <-> is_true (P0 y).
  Proof.
    intros x y Hxy. split; intro H; rewrite <- P0_spec; intros Y Hi Hs HP; rewrite HP.
      rewrite <- P0_spec in H; apply H; try assumption. now symmetry.
      rewrite <- P0_spec in H; apply H; try assumption. now symmetry.
  Qed.

  Lemma P0_is_invariant_subCPO : is_true (Invariant F P0) /\ is_true (is_subCPO P0).
  Proof.
    split.
    + apply BForall_spec. setoid_rewrite <- BImpl_spec. intros x H.
      unfold Image in H. rewrite <- BExists_spec in H. destruct H as [x0 H]. rewrite <- BAnd_spec in H.
      apply P0_preserves_weq with (F x0). apply H. rewrite <- P0_spec. intros Y Hi Hs HP. destruct H. rewrite <- P0_spec in H.
      unfold Invariant in Hi. rewrite included_spec in Hi. apply Hi. apply BExists_spec. exists x0.
      apply BAnd_spec. split. apply H. apply included_spec. apply Hi. apply Hs. apply HP.
      now fold_weq.
    + apply is_subCPO_spec. intros D H. rewrite <- P0_spec. intros Y Hi Hs HP. rewrite <- is_subCPO_spec in Hs. apply Hs.
      rewrite included_spec. rewrite included_spec in H. intros x Hx. specialize H with x. 
      apply H in Hx. rewrite <- P0_spec in Hx. apply Hx. apply Hi. apply is_subCPO_spec. apply Hs. apply HP.
  Qed.

  Lemma P0_is_smallest_invariant_subCPO : forall Y, is_true (Invariant F Y) -> is_true (is_subCPO Y)
    -> (forall x y, x == y -> is_true (Y x) <-> is_true (Y y)) -> is_true (included P0 Y).
  Proof. intros Y Hi Hs HP. apply included_spec. intros x Hx. rewrite <- P0_spec in Hx. now apply Hx. Qed.

End Invariant_subCPOs.



(** * Common fixpoint of every monotonous increasing function *)

Section Increasing_fixpoint.
  Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {P : B_CPO P'}.

  Definition Increasing F := BForall X (fun x => leq x (F x)).
(* All the below work in this section, on the CPO of Monotonous function on a CPO is unused.
  We had to find a way to not need to define a subset as a CPO, cf "mon_fun_applied".
  This is to avoid defining type-dependent objects in our truth values B. *)
  Definition Increasing_restricted Y F := BAnd (Invariant F Y) (BForall X (fun x => BImpl (Y x) (leq x (F x)))).

  Definition leq_mon f g := (@leq B valid_mon_type B_PO_mon f g).
  Definition weq_mon f g := (@weq B valid_mon_type B_PO_mon f g).

  Program Definition Increasing_functions := exist (Directed_in_prop leq_mon) (Increasing) _.
  Next Obligation.
    apply Directed_spec. unfold_spec. intros f g Hf Hg. exists (comp f g). 
    repeat split.
    + intros x. fold_leq. cbn. destruct g as [g gmon]; cbn in *. transitivity (g x). apply Hg. apply Hf. 
    + destruct f as [f fmon]; cbn in *. apply BForall_spec. intro x. fold_leq.
      rewrite <- BMonotony_spec in fmon. apply fmon. apply Hg.
    + cbn. apply BForall_spec. intro x. cbn. apply Hf.
  Defined.

  Definition H_sup := (sup (B_CPO := B_CPO_mon) Increasing_functions).

  Lemma H_sup_is_increasing : is_true (Increasing (FBody H_sup)).
  Proof. apply BForall_spec. intro. assert (is_true (leq_mon id H_sup)).
   apply (sup_spec (B_CPO := B_CPO_mon) Increasing_functions). reflexivity.
   unfold Increasing_functions. cbn. apply BForall_spec. intro.
   now fold_leq.
   cbn in H. rewrite <- BForall_spec in H. apply H. 
  Qed.

  Lemma H_sup_bot_is_fixpoint_of_all_Increasing (F:mon) :
    is_true (Increasing F) -> is_true (Fix F ((FBody H_sup) bot)).
  Proof.
    intro. setoid_rewrite <- BForall_spec in H. assert (is_true (weq_mon (comp F H_sup) H_sup)).
    + apply weq_spec. split. apply (sup_spec (B_CPO := B_CPO_mon) Increasing_functions). reflexivity.
      unfold Increasing_functions. cbn. apply BForall_spec. intro x. fold_leq. transitivity ((FBody H_sup) x).
      transitivity ((FBody H_sup) x). pose proof H_sup_is_increasing.
      setoid_rewrite <- BForall_spec in H0. apply H0. reflexivity. cbn.
      apply H. unfold leq_in_prop. cbn. apply BForall_spec. intro x. apply H.
    + unfold Fix. cbn in H0. rewrite <- BForall_spec in H0. apply H0.
  Qed.

  (* Lemma 8.21*)
  Lemma increasing_has_fix_point (F:mon) : is_true (Increasing F) -> exists x, is_true (Fix F x).
  Proof.
    intro. exists ((FBody H_sup) bot). now apply H_sup_bot_is_fixpoint_of_all_Increasing.
  Qed.

End Increasing_fixpoint.



Section Fixpoint_II.
  Context {B : B_param} {X : valid_type} {P' : @B_PO B X} {P : B_CPO P'}.

  Definition is_least S x := is_true (S x) /\ forall y, is_true (S y) -> x <= y.
  Definition is_inf S x := forall z, (forall y, is_true (S y) -> z <= y) <-> z <= x.
  Definition is_minimal S x := is_true (S x) /\ forall y, is_true (S y) -> y <= x -> y == x.
  Definition is_greatest S x := is_true (S x) /\ forall y, is_true (S y) -> y <= x.
  Definition is_maximal S x := is_true (S x) /\ forall y, is_true (S y) -> x <= y -> y == x.
  Definition is_sup S x := forall z, (forall y, is_true (S y) -> y <= z) <-> x <= z.


  Variable F:mon.
  Let P0_memo := memo X (P0 F).
  
  (** * Fixpoint theorems and proofs : second theorem. *)

  Lemma Induction_Rule : (exists ??0, is_least (Pre F) ??0)
                         -> exists ??, is_least (Fix F) ?? /\ forall x, is_true (Pre F x) -> ?? <= x.
  Proof.
    intro H. destruct H as [??0 Hmu0].
    exists ??0. repeat split.
    + apply weq_spec. split. apply Hmu0.
      apply Hmu0. unfold Pre. destruct F as [Ff Fmon]. cbn in *.
      rewrite <- BMonotony_spec in Fmon. apply Fmon. apply Hmu0.
    + intros. apply Hmu0. now apply fix_is_pre.
    + apply Hmu0.
  Qed.

  Lemma P0_is_in_Post : is_true (included (P0 F) (Post F)).
  Proof.
    assert (is_true (Invariant F (Post F)) 
         /\ is_true (is_subCPO (Post F)) 
         /\ (forall x y, x == y -> is_true ((Post F) x) <-> is_true ((Post F) y))).
    + repeat split.
    - apply BForall_spec. setoid_rewrite <- BImpl_spec. intros x H.
      setoid_rewrite <- BExists_spec in H. setoid_rewrite <- BAnd_spec in H. destruct H as [x0 [Px0 Fx]].
      unfold Post. fold_leq. rewrite Fx. destruct F as [Ff Fmon]. cbn in *. rewrite <- BMonotony_spec in Fmon.
      apply Fmon. apply Px0.
    - apply is_subCPO_spec. setoid_rewrite included_spec. intros D H. apply sup_spec. intros.
      transitivity (F y). now apply H. destruct F as [Ff Fmon]. cbn in *. rewrite <- BMonotony_spec in Fmon.
      apply Fmon. now apply leq_xsup.
    - unfold Post. fold_leq. intro Hx. fold_leq. now rewrite <- H.
    - unfold Post. fold_leq. intro Hx. fold_leq. now rewrite H.
      + now apply P0_is_smallest_invariant_subCPO.
  Qed.

  Lemma P0_is_in_down x : is_true (Fix F x) -> is_true (included (P0 F) (down x)).
  Proof.
    intro. assert (is_true (Invariant F (down x)) 
                /\ is_true (is_subCPO (down x))
                /\ (forall z y, z == y -> is_true ((down x) z) <-> is_true ((down x) y))).
    + repeat split.
    - unfold_spec.
      intros y Hy. destruct Hy as [x0 [Dx0 Fyx0]]. unfold down. fold_leq. unfold Fix in H.
      rewrite <- H. rewrite Fyx0. destruct F as [Ff Fmon]. cbn in *. rewrite <- BMonotony_spec in Fmon.
      apply Fmon. apply Dx0.
    - apply down_is_subCPO.
    - unfold down. fold_leq. intro Hzx. fold_leq. now rewrite <- H0.
    - unfold down. fold_leq. intro Hzx. fold_leq. now rewrite H0.
      + now apply P0_is_smallest_invariant_subCPO.
  Qed.



(* ------ Dodging subCPOs, to avoid type-dependent objects ------ *)

 Definition mon_fun_applied (Y : X -> B) (z : X) (x0 : X) := 
  BExists (valid_fun_type) (fun h => BAnd (weq x0 (h z)) 
                       (BAnd (BForall X (fun x => BForall X (fun y => BImpl (Y x) (BImpl (Y y) (BImpl (leq x y) (leq (h x) (h y))) ))))
                       (BAnd (BForall X (fun x => BImpl (Y x) (leq x (h x))))
                       (BAnd (BForall X (fun x => BImpl (Y x) (Y (h x))))
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
  exists (hx (hy z)). repeat split. exists (fun x => hx (hy x)).
  + repeat split.
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
   -> (forall x y, weq_in_prop x y -> (is_true (Y x) <-> is_true (Y y)))
   -> is_true (mon_fun_applied Y bot (sup (fun_on_Y_subCPO Y bot))).
 Proof. unfold is_subCPO. setoid_rewrite <- BForall_spec.
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
 
 Definition lfp_II := (sup (fun_on_Y_subCPO P0_memo bot)).
 
 Lemma P0_memo_preserves_weq : forall (x y : X),
       x == y -> is_true (P0_memo x) <-> is_true (P0_memo y).
 Proof. unfold P0_memo. setoid_rewrite memo_spec. apply P0_preserves_weq. Qed.

 Theorem Fixpoint_II_no_subCPO : is_true (Fix F lfp_II).
 Proof.
 unfold lfp_II. pose proof (P0_is_invariant_subCPO F) as [PI PS].
 assert (is_true ((P0 F) (sup (fun_on_Y_subCPO P0_memo bot)))).
 rewrite <- is_subCPO_spec in PS.
 apply PS. apply included_spec. cbn. setoid_rewrite <- mon_fun_spec.
 intros x Hx. destruct Hx as [hx [Hhx [hxmon [hxinc [hxinv HYx]]]]].
 apply P0_preserves_weq with (hx bot). apply Hhx.
 rewrite <- memo_spec. apply hxinv. assumption.
 
 unfold Fix. fold_weq. apply weq_spec. split.
 
 + assert (is_true (is_subCPO P0_memo)) as PS_memo. 
   apply is_subCPO_spec. intros D H0. unfold P0_memo. rewrite memo_spec. rewrite <- P0_spec.
   intros Y Hi Hs HP. rewrite <- is_subCPO_spec in Hs. apply Hs.
      rewrite included_spec. rewrite included_spec in H0. intros x Hx. specialize H0 with x. 
      apply H0 in Hx. unfold P0_memo in Hx. rewrite memo_spec in Hx. rewrite <- P0_spec in Hx.
      apply Hx. apply Hi. apply is_subCPO_spec. apply Hs. apply HP.
 
   pose proof (set_of_fun_is_subCPO P0_memo PS_memo) as Hsub. rewrite <- mon_fun_spec in Hsub.
   destruct Hsub as [hx [Hhx [hxmon [hxinc [hxinv HYx]]]]]. apply P0_memo_preserves_weq.
   rewrite Hhx at 1. apply leq_xsup. cbn. rewrite <- mon_fun_spec. exists (fun x => F (hx x)). repeat split. 
  - fold_weq. reflexivity.
  - intros x y Hx Hy Hxy. clear H. clear Hhx. destruct F as [Ff Fmon]. cbn in *. rewrite <- BMonotony_spec in Fmon.
    apply Fmon. now apply hxmon.
  - intros x Hx. fold_leq. transitivity (hx x). now apply hxinc.
    pose proof P0_is_in_Post. rewrite included_spec in H0. apply H0. unfold P0_memo in *. 
    setoid_rewrite memo_spec in hxinv. apply hxinv. now apply memo_spec.
  - intros x Hx. unfold Invariant in PI. rewrite included_spec in PI.
    unfold P0_memo in *. rewrite memo_spec. apply PI. unfold Image.
    rewrite <- BExists_spec. setoid_rewrite <- BAnd_spec.
    exists (hx x). split. setoid_rewrite memo_spec in hxinv. apply hxinv. now apply memo_spec. fold_weq. reflexivity.
  - assumption. 
 + pose proof P0_is_in_Post. rewrite included_spec in H0. apply H0.
   rewrite <- is_subCPO_spec in PS. apply PS. rewrite included_spec. cbn.
   setoid_rewrite <- mon_fun_spec. intros x Hx. 
   destruct Hx as [hx [Hhx [hxmon [hxinc [hxinv HYx]]]]].
   apply P0_preserves_weq with (hx bot). apply Hhx.
   unfold P0_memo in *. setoid_rewrite memo_spec in hxinv. apply hxinv. now apply memo_spec.
 Qed.


End Fixpoint_II.



Section Bourbaki_Witt.

  Context {B : B_param} {X : valid_type} `{P : B_CPO (B := B) (X := X)}.
  
  (* axioms *)
  Definition classic_axiom := forall (P : Prop), P \/ ~ P.
  
  Definition weak_classic_axiom := forall (R P Q: X -> Prop), (forall x, R x -> (P x \/ Q x)) 
    -> (forall x, R x -> P x) \/ (exists x, R x /\ Q x).
  Lemma classic_axiom_implies_weak_classic_axiom : classic_axiom -> weak_classic_axiom.
  Proof. 
    intros EM S Q R H. destruct (EM (exists x : X, S x /\ R x)). now right. left.
    intros x Sx. destruct (H x). assumption. assumption. contradict H0. now exists x.
  Qed.
  
  Definition decidable_weq := forall (x y : X), (x == y) \/ ~(x==y).
  Lemma classic_axiom_implies_decidable_weq : classic_axiom -> decidable_weq.
  Proof. intros EM x y. now destruct (EM (x == y)). Qed.
  
  Definition is_Chain (Y : X -> B) := forall (x y : X), is_true (Y x) -> is_true (Y y) -> x <= y \/ y <= x.

  Lemma chain_is_directed : forall D, is_Chain D -> is_true (Directed leq D).
  Proof.
    setoid_rewrite <- Directed_spec.
    intros D Hd x y Hx Hy. destruct (Hd x y); intuition.
    exists y. repeat split; intuition. fold_leq. reflexivity.
    exists x. repeat split; intuition. fold_leq. reflexivity.
  Qed.
  

  (* Now show that P0 is a chain, to prove that it has a sup (top). This is a fixpoint. *)

  Definition lt x y := BAnd (leq x y) (BImpl (weq x y) BFalse).
  Lemma lt_spec : forall x y, ((x <= y) /\ (~ x == y)) <-> is_true (lt x y).
  Proof. unfold_spec. intuition. now apply BFalse_spec. Qed.
  
  Definition lt_in_prop x y := is_true (lt x y).
  Infix "<" := lt_in_prop.

  Lemma leq_is_lt_or_eq : decidable_weq -> forall x y, x <= y -> x == y \/ x < y. (* excluded middle ! *)
  Proof. intros EM x y Hxy. destruct (EM x y). now left. right. now apply lt_spec. Qed.

  Lemma not_leq_and_gt : forall x y, ~ (x <= y /\ y < x). (* no need for EM *)
  Proof. intros x y. intro. destruct H. apply lt_spec in H0. destruct H0. contradict H1. now apply weq_spec. Qed.

  Definition Extreme F' : X -> B :=
     (fun c => BAnd ((P0 F') c) 
                    (BForall X (fun x => BImpl ((P0 F') x) 
                                                (BImpl (lt x c) (leq (F' x) c))))).
  Lemma Extreme_spec F' : forall c,
    (is_true (P0 F' c) /\ forall x, is_true (P0 F' x) -> x < c -> F' x <= c) <-> is_true (Extreme F' c).
  Proof. unfold_spec. tauto. Qed.

  Definition Mc F' c : (X -> B) :=
    (fun x => BAnd (P0 F' x) (BOr (leq x c) (leq (F' c) x))).
  Lemma Mc_spec F' c : forall x,
    (is_true (P0 F' x) /\ (x <= c \/ F' c <= x)) <-> is_true (Mc F' c x).
  Proof. unfold_spec. tauto. Qed.
  
  
  Variable F' : X -> X.
  Hypothesis F'_preserves_weq : forall x y, x == y -> F' x == F' y.

  Lemma Mc_is_P0 : weak_classic_axiom -> decidable_weq -> is_true (Increasing F') 
    -> forall c, is_true (Extreme F' c) 
    -> is_true (set_eq (P0 F') (Mc F' c)).
  Proof.
    destruct P0_is_invariant_subCPO with F' as [Hi Hs]. unfold Invariant in Hi.
    rewrite included_spec in Hi. rewrite <- is_subCPO_spec in Hs.    
    pose proof P0_is_smallest_invariant_subCPO as HP0. setoid_rewrite included_spec in HP0.
    
    intros EM eq_dec HF c Ec. apply Extreme_spec in Ec. destruct Ec as [Pc Ec'].
    unfold Increasing in HF. rewrite <- BForall_spec in HF.
    apply BForall_spec. setoid_rewrite <- BEq_spec. split.
    + apply HP0.
      - intros y Hy. rewrite <- Image_spec in Hy. inversion Hy.
        destruct H as [H Hyx0]. rewrite <- Mc_spec in H. destruct H as [Px0 Hx0].
        apply Mc_spec. split. apply Hi. rewrite <- Image_spec. exists x0.
        split. apply Px0. assumption. destruct Hx0.
        * apply leq_is_lt_or_eq in H. destruct H. right. apply weq_spec. rewrite Hyx0.
          now apply F'_preserves_weq.
          left. rewrite Hyx0. now apply Ec'. assumption.
        * right. transitivity x0. assumption. rewrite Hyx0. apply HF.
      - intros D Hinc. destruct D as [D HD]. rewrite included_spec in Hinc.
        setoid_rewrite <- Mc_spec in Hinc. apply Mc_spec. split.
        apply Hs. rewrite included_spec. intros x0 Dx0.
        apply Hinc in Dx0. apply Dx0.
        destruct (EM (fun z => is_true (D z)) (fun z => z <= c) (fun z => F' c <= z)). (* WARNING : excluded middle ! *)
        * apply Hinc.
        * left. apply sup_spec. now apply H.
        * right. destruct H as [y Hy]. transitivity y. apply Hy. now apply leq_xsup.
      - intros y1 y2 Hy12. setoid_rewrite <- Mc_spec. split; intros; destruct H as [HP0y HOr]; split.
        now apply P0_preserves_weq with y1. destruct HOr; [left | right]; now rewrite <- Hy12.
        now apply P0_preserves_weq with y2. destruct HOr; [left | right]; now rewrite Hy12.
    + intro Hm. rewrite <- Mc_spec in Hm. apply Hm.
  Qed.

  Lemma P0_is_extreme : weak_classic_axiom -> decidable_weq -> is_true (Increasing F') 
    -> forall x, is_true (P0 F' x) -> is_true (Extreme F' x).
  Proof.
    destruct P0_is_invariant_subCPO with F' as [Hi Hs]. unfold Invariant in Hi.
    rewrite included_spec in Hi. rewrite <- is_subCPO_spec in Hs.    
    pose proof P0_is_smallest_invariant_subCPO as HP0. setoid_rewrite included_spec in HP0.
    
    intros EM eq_dec HF.
    apply HP0. clear HP0.
    + intros c Hc. rewrite <- Image_spec in Hc. destruct Hc. destruct H as [HPx HEx].
      rewrite <- Extreme_spec in HPx.
      apply Extreme_spec. split.
    - apply Hi. rewrite <- Image_spec. exists x. split. apply HPx. assumption.
    - intros. assert (is_true (set_eq (P0 F') (Mc F' x))). apply (Mc_is_P0 EM eq_dec HF).
      rewrite <- Extreme_spec. apply HPx.
      assert (is_true (Mc F' x x0)). unfold set_eq in H1. rewrite <- BForall_spec in H1.
      setoid_rewrite <- BEq_spec in H1. apply H1. apply H.
      
      rewrite <- Mc_spec in H2. destruct H2. destruct H3.
      * rewrite HEx. apply leq_is_lt_or_eq in H3; intuition.
        apply weq_spec. now apply F'_preserves_weq. transitivity x; intuition.
        unfold Increasing in HF. rewrite <- BForall_spec in HF. apply HF.
      * exfalso. eapply not_leq_and_gt. split. rewrite <- HEx in H3. apply H3. assumption.
      + clear HP0. intros D Ed. apply Extreme_spec.
        split. apply Hs. rewrite included_spec in Ed. apply included_spec. intros x Hx.
        apply Ed in Hx. rewrite <- Extreme_spec in Hx. apply Hx.
        intros x Px Hxd. destruct D as [D HD]. destruct (EM (fun z => is_true (D z)) (fun z => z <= x) (fun z => x <= z)). (*destruct (EM (exists c, is_true (D c) /\ x <= c)).*)
    - cbn in *. intros c Hdc. pose proof (Mc_is_P0 EM eq_dec HF c). unfold set_eq in H.
        setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BEq_spec in H.
        destruct H with x. rewrite included_spec in Ed. now apply Ed. apply H0 in Px.
        rewrite <- Mc_spec in Px. destruct Px. destruct H3. now right. left. rewrite <- H3.
        unfold Increasing in HF. rewrite <- BForall_spec in HF. apply HF.
    - assert (sup (exist (fun Dbody0 : X -> B => Directed_in_prop leq Dbody0) D HD) <= x).
      * apply sup_spec. intros. cbn in *. now apply H.
      * exfalso. eapply not_leq_and_gt. split. apply H0. assumption.
    - destruct H as [c [Hdc Hcx]]. apply leq_is_lt_or_eq in Hcx; intuition.
      * transitivity (F' c). apply weq_spec. now apply F'_preserves_weq.
        assert (is_true (Mc F' c (sup (exist (fun Dbody0 : X -> B => Directed_in_prop leq Dbody0) D HD)))).
        pose proof (Mc_is_P0 EM eq_dec HF c). unfold set_eq in H0.
        setoid_rewrite <- BForall_spec in H0. setoid_rewrite <- BEq_spec in H0.
        apply H0. rewrite included_spec in Ed. apply Ed. apply Hdc.
        apply Hs. apply included_spec. intros y Hy. rewrite included_spec in Ed.
        apply Ed in Hy. rewrite <- Extreme_spec in Hy. apply Hy.
        rewrite <- Mc_spec in H0.
        destruct H0. destruct H1. exfalso. eapply not_leq_and_gt. split. rewrite <- H in H1.
        apply H1. apply Hxd. assumption.
      * transitivity c. rewrite included_spec in Ed. cbn in *. apply Ed in Hdc.
        rewrite <- Extreme_spec in Hdc. now apply Hdc. now apply leq_xsup.
    + intros y1 y2 Hy12. setoid_rewrite <- Extreme_spec. split; intros; destruct H as [HP0y HImp]; split.
        now apply P0_preserves_weq with y1. intros x HP0x Hxy2. rewrite <- Hy12. apply HImp. assumption.
        apply lt_spec. apply lt_spec in Hxy2. now rewrite Hy12.
        now apply P0_preserves_weq with y2. intros x HP0x Hxy1. rewrite Hy12. apply HImp. assumption.
        apply lt_spec. apply lt_spec in Hxy1. now rewrite <- Hy12.
  Qed.


  Lemma P0_is_Chain : weak_classic_axiom -> decidable_weq -> is_true (Increasing F') -> is_Chain (P0 F').
  Proof.
    intros EM eq_dec HF x y Hx Hy. assert (is_true (Mc F' x y)).
    pose proof (Mc_is_P0 EM eq_dec HF x). unfold set_eq in H.
    setoid_rewrite <- BForall_spec in H. setoid_rewrite <- BEq_spec in H.
    apply H.
    apply P0_is_extreme; intuition. assumption.
    rewrite <- Mc_spec in H. destruct H. destruct H0. now right. left. transitivity (F' x).
    unfold Increasing in HF. rewrite <- BForall_spec in HF. apply HF.
    assumption.
  Qed.

  Lemma P0_is_directed : weak_classic_axiom -> decidable_weq -> is_true (Increasing F') -> is_true (Directed leq (P0 F')).
  Proof. intros EM eq_dec HF. apply chain_is_directed. now apply P0_is_Chain. Qed.

  (* Note : since we put excluded middle and functional extensionality as hypothesis, we lose constructivity,
we can't just define our fixpoint as below :
Program Definition top_P0 (F':X -> X) (H : Increasing F') := (sup (exist _ (P0 F') _)).
Next Obligation. apply P0_is_directed; intuition. apply H. Qed. *)

  (* The book is wrong : the top of P0 is not necessarily minimal (cf counterexample on paper and in work_prop.v) *)
  Theorem Fixpoint_III : weak_classic_axiom -> decidable_weq -> is_true (Increasing F') -> exists x, is_true (Fix F' x) (*is_minimal (Fix F') x*).
  Proof.
    destruct P0_is_invariant_subCPO with F' as [Hi Hs]. unfold Invariant in Hi.
    rewrite included_spec in Hi. rewrite <- is_subCPO_spec in Hs.
    
    intros EM eq_dec HF. exists (sup (exist _ (P0 F') (P0_is_directed EM eq_dec HF))).
    apply weq_spec. split. apply leq_xsup; cbn. apply Hi. 
    rewrite <- Image_spec. exists (sup
       (exist (fun Dbody0 : X -> B => Directed_in_prop leq Dbody0) 
          (P0 F') (P0_is_directed EM eq_dec HF))). split. apply Hs. cbn. now apply included_spec. cbn.
    reflexivity.
    apply sup_spec; cbn. intros.
    assert (forall x, x <= F' x) as HF'. apply BForall_spec. apply HF. rewrite <- HF'.
    now apply leq_xsup.
  Qed.

End Bourbaki_Witt.

(*
Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extraction "lfp.ml" lfp_II. 
*)


