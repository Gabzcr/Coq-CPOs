From Coq Require Import Arith.
Require Import Psatz.
Require Export Setoid Morphisms.
Set Implicit Arguments.


(* Definition of Directed sets for some order relation <=. D is directed if :
forall x y in D, there is a z in D such that x <= z and y <= z. *)

Notation set X := (X -> Prop).
Notation rel X := (X -> X -> Prop).
Definition Directed {X} `(leq : rel X) (D : set X) : Prop :=
  forall x y, D x -> D y -> exists z, D z /\ leq x z /\ leq y z.
Definition directed_set {X} (leq : rel X) := {Dbody : set X | Directed leq Dbody}.
Definition Dbody {X leq} (D : directed_set leq) : set X := proj1_sig D.
Coercion Dbody : directed_set >-> Funclass.

Class PO (X: Type) := {
    weq : relation X;
    leq: relation X;
    PreOrder_leq:> PreOrder leq;
    weq_spec: forall x y, weq x y <-> (leq x y /\ leq y x);
  }.

(* Definition of a CPO : Complete Partially Ordered set*)
Class CPO (X: Type) `(P' : PO X) := {
    sup: directed_set leq -> X -> Prop;
    sup_spec: forall D d, sup D d <-> (forall z, (leq d z <-> forall (y:X), D y -> leq y z));
    sup_exists : forall D, exists d, sup D d (*restricted to directed set as here*)
  }.

(* Definition of Lattice as a particular (stronger) CPO. *)
Class CompleteLattice (X : Type) `(L' : PO X) := {
    supL: (X -> Prop) -> X -> Prop;
    sup_specL: forall Y d, supL Y d <-> (forall z, (leq d z <-> forall (y:X), Y y -> leq y z));
    sup_existsL : forall D, exists d, supL D d (*restricted to directed set as here*)
  }.

(* Scopes are a way to guide parsing when overloading a symbol.
   See: https://coq.inria.fr/distrib/current/refman/user-extensions/syntax-extensions.html#notation-scopes
 *)
Declare Scope CPO. (* I don't really understand there 2 lines. *)
Open Scope CPO.
Infix "==" := weq (at level 70): CPO.
Infix "<=" := leq: CPO.
#[global] Hint Extern 0 => reflexivity: core.

(** * Utilities  *)

(** any monotone function preserves equality  *)
Lemma op_leq_weq_1 {X Y} {LX: PO X} {LY: PO Y} {f: X -> Y}
      {Hf: Proper (leq ==> leq) f}: Proper (weq ==> weq) f.
Proof. intros x y. rewrite 2weq_spec. intro E; split; apply Hf; apply E. Qed.

Lemma op_leq_weq_2 {X Y Z} {LX: PO X} {LY: PO Y} {LZ: PO Z} {f: X -> Y -> Z}
      {Hf: Proper (leq ==> leq ==> leq) f}: Proper (weq ==> weq ==> weq) f.
Proof.
  intros x y E x' y' E'. rewrite weq_spec in E. rewrite weq_spec in E'.
  apply weq_spec. split; apply Hf; (apply E || apply E').
Qed.


(** * Sets general properties *)

Section Sets.

  Context {X} {P' : PO X}.

  Definition set_eq (f g : X -> Prop) := forall z, f z <-> g z. (*equality of sets*)

  Definition included (S T: set X) := forall x, S x -> T x.

  #[global] Instance Included_trans : Transitive included.
  Proof.
    intros Y1 Y2 Y3 H12 H13. intros x H. apply H13. now apply H12.
  Qed.

End Sets.
Infix "⊆" := included (at level 70).


(** * Directedness general properties *)

Section Directedness.

  Context {X} {P' : PO X}.

  Lemma directed_symmetry f g : (forall z, f z <-> g z) -> Directed leq f <-> Directed leq g.
  Proof. intro H. unfold Directed. setoid_rewrite H. tauto. Qed.

  #[global] Instance directed_eq : Proper (set_eq ==> iff) (Directed leq).
  Proof. intros f g. apply directed_symmetry. Qed.

  Lemma singleton_is_directed x : Directed leq (fun z => z=x).
  Proof. unfold Directed. intros y z Hyz. exists x. repeat split. now rewrite Hyz. now rewrite H. Qed.

  Definition is_Chain (Y : set X) := forall (x y : X), Y x -> Y y -> x <= y \/ y <= x.

  Lemma chain_is_directed : forall D, is_Chain D -> Directed leq D.
  Proof.
    intros D Hd x y Hx Hy. destruct (Hd x y); intuition.
    exists y. now split.
    exists x. now split.
  Qed.

End Directedness.

(** Partial Order general properties *)

Section Partial_order.

  Context {X} {P' : PO X}.

  #[global] Instance Equivalence_weq: Equivalence weq.
  Proof.
    constructor.
    intro x. now apply weq_spec.
    intros x y. rewrite 2weq_spec. tauto.
    intros x y z. rewrite 3weq_spec. split; transitivity y; tauto.
  Qed.

  #[global] Instance PartialOrder_weq_leq: PartialOrder weq leq.
  Proof.
    intros x y. simpl. now rewrite weq_spec.
  Qed.

  Lemma antisym x y: x <= y -> y <= x -> x == y.
  Proof. rewrite weq_spec. tauto. Qed.

  Lemma from_above x y: (forall z, x<=z <-> y<=z) -> x==y.
  Proof. intro E. apply antisym; apply E; reflexivity. Qed.

  Lemma from_below x y: (forall z, z<=x <-> z<=y) -> x==y.
  Proof. intro E. apply antisym; apply E; reflexivity. Qed.

End Partial_order.


(** * General properties of the sup operation. *)

Section sup.

  Context {X} {P' : PO X} {P: CPO P'} {L : CompleteLattice P'}.

  Lemma leq_xsup (D : directed_set _) y: D y -> forall d, sup D d -> y <= d.
  Proof. intros H d Sd. now apply (sup_spec D d). Qed.

  Lemma leq_xsupL (Y:X->Prop) y : Y y -> forall d, supL Y d -> y <= d.
  Proof. intros H d Sd. now apply (sup_specL Y d). Qed.

  Lemma sup_is_independent_of_proof : forall D_dir D_dir2,
      set_eq (Dbody D_dir) (Dbody D_dir2) -> forall d, sup D_dir d <-> sup D_dir2 d.
  Proof.
    intros D1 D2 H d. split; intro; apply sup_spec; intros. split; intros.
    + transitivity d. apply leq_xsup with D1; intuition. now apply H. assumption.
    + rewrite sup_spec in H0. apply H0. intros. apply (H1 y). now apply H.
    + split; intros. transitivity d. apply leq_xsup with D2; intuition. now apply H. assumption.
      rewrite sup_spec in H0. apply H0. intros. apply (H1 y). now apply H.
Qed.

  Program Definition empty : directed_set leq :=
    exist _ (fun _ => False) _.
  Next Obligation. unfold Directed. intros. contradict H. Defined.

  Definition is_bot := sup empty. (*Warning : with our current definition of directed,
 bottom exists since the empty set is directed. Later, we might want to change that to allow bottom to no exist*)

  Lemma bot_spec: forall x bot, is_bot bot -> bot <= x.
  Proof. intros. now apply (sup_spec empty bot). Qed.
  
  Lemma exists_bot : exists bot, is_bot bot.
  Proof. destruct (sup_exists empty) as [bot Hbot]. now exists bot. Qed.

  Program Definition full : set X := (fun _ => True).
  Definition is_topL := supL (fun _ => True). (* Rmk : only exists in lattices, not just CPOs. *)

  Lemma top_specL: forall x top, is_topL top -> x <= top.
  Proof. intro. now apply leq_xsupL. Qed.
  
  Lemma exists_topL : exists top, is_topL top.
  Proof. destruct (sup_existsL full) as [top Htop]. now exists top. Qed.

  (** Inf *)
(*
  Definition inf_lat Y := supL (fun z => forall y, Y y -> z <= y).
  Lemma inf_spec_lat: forall Y z, z <= inf_lat Y <-> (forall y, Y y -> z <= y).
  Proof.
    intros. unfold sup. split.
    intros H y Yy. rewrite H; apply sup_specL. now auto.
    intro. now apply leq_xsupL.
  Qed.

  Lemma leq_xinf (D: X -> Prop) y:  D y -> inf_lat D <= y.
  Proof. intro H. now apply inf_spec_lat with D. Qed.
*)

  Lemma sup_unicity : forall D d1 d2, sup D d1 -> sup D d2 -> d1 == d2.
  Proof.
    intros D d1 d2 H1 H2. apply weq_spec. split; eapply sup_spec.
    apply H1. now apply sup_spec with d2. 
    apply H2. now apply sup_spec with d1.
  Qed.


  (* --- Inclusion of sets and sup --- *)

  Definition included_body (S T : directed_set leq) := S ⊆ T.

(* To be redefined without a Proper *)
(*
  #[global] Instance sup_preserves_inclusion: Proper (included_body ==> leq) sup.
  Proof.
    intros S T HST. apply sup_spec. intros. apply leq_xsup.
    now apply HST.
  Qed.
*)

  Lemma sup_preserves_inclusion : forall (D1 D2 : directed_set leq) d1 d2, included D1 D2 -> sup D1 d1 -> sup D2 d2 -> d1 <= d2.
  Proof.
  intros S T d1 d2 HST Hd1 Hd2. eapply sup_spec. apply Hd1. intros. eapply leq_xsup. now apply HST. assumption. Qed.

  Definition set_eq_body (S T : directed_set leq) := set_eq S T.
(*
  #[global] Instance sup_preserves_equality: Proper (set_eq_body ==> weq) sup.
  Proof.
    intros S T HST. apply weq_spec. split; apply sup_preserves_inclusion; intros x Hx; now apply HST.
  Qed.
*)

End sup.

#[global] Hint Resolve bot_spec: core.


(** * Monotonous functions and other properties *)

Section functions.
  Context {X} `{P: CPO X}.

  Definition Fix F x := F x == x.
  Definition Post F x := x <= F x.
  Definition Pre F x := F x <= x.

  Lemma fix_is_post F : forall x, Fix F x -> Post F x.
  Proof. intros. apply weq_spec in H. apply H. Qed.
  Lemma fix_is_pre F : forall x, Fix F x -> Pre F x.
  Proof. intros. apply weq_spec in H. apply H. Qed.


  (* Monotonous functions *)

  Record mon := { body:> X -> X; Hbody: Proper (leq ==> leq) body }.
  Record mon_prop := { body_prop:> X -> X -> Prop ; 
                       Hbody_prop: forall x y, x <= y -> forall fx fy, body_prop x fx -> body_prop y fy -> fx <= fy ;
                       Hfun: forall x, exists y, body_prop x y /\ forall y', (body_prop x y' <-> y == y')
                     }.
 
  Program Definition from_mon (F:mon) : mon_prop :=
    {|
      body_prop x y := y == F x;
    |}.
  Next Obligation. rewrite H0, H1. now apply Hbody. Qed.
  Next Obligation. now exists (F x). Qed.

  Definition is_correct (f:mon_prop) := forall x1 x2 y, x1 == x2 -> (f x1 y) <-> (f x2 y).

  #[global] Instance Hbody' (F:mon) : Proper (weq ==> weq) F.
  Proof. apply (op_leq_weq_1 (Hf:=(Hbody F))). Qed.
  
  #[global] Lemma Hbody_prop' (F:mon_prop) : forall x y1 y2, y1 == y2 ->  (F x y1 <-> F x y2).
  Proof. intros. destruct (Hfun F x) as [y [? ?]]. split; intro; apply H1. rewrite <- H. now apply H1.
  rewrite H. now apply H1. Qed.


  Definition Fix_prop (F : mon_prop) x := F x x.
  Definition Post_prop (F : mon_prop) x := forall y, F x y -> x <= y.
  Definition Pre_prop (F : mon_prop) x := forall y, F x y -> y <= x.

  Variant Image f (S : X -> Prop) : X -> Prop :=
  |from_image : forall x, S x -> Image f S (f x).

  Definition Continuous f :=
    forall (D : set X) (H : Directed leq D),
      {dir_im : Directed leq (Image f D) & 
                forall di df, sup (exist _ D H ) di -> sup (exist _ (Image f D) dir_im) df
                  -> f di == df}.

  Lemma mon_preserves_directedness_and_sup (F:mon) :
    forall (D : set X) (H : Directed leq D),
      {dir_im : Directed leq (Image F D) &
                 forall di df, sup (exist _ D H ) di -> sup (exist _ (Image F D) dir_im) df
                  -> df <= F di}.
  Proof.
    intros. assert (Directed leq (Image F D)).
    + unfold Directed. intros. inversion H0. inversion H1.
      destruct (H x0 x1); try assumption. exists (F x2).
      repeat split; try apply Hbody; apply H6.
    + exists H0. intros di df Hdi Hdf. eapply sup_spec. apply Hdf. cbn. intros.
      inversion H1. apply Hbody. apply (leq_xsup (exist (Directed leq) D H)); now cbn.
  Qed.

  (* Some basic monotonous functions *)

  Program Definition const x: mon := {| body y := x |}.
  Next Obligation. intros ? ? ?. reflexivity. Qed.

  Definition id: mon := {|
                         body x := x;
                         Hbody x y H := H
                       |}.
  Program Definition id_prop: mon_prop := {|
                       body_prop x y := x == y;
                     |}.
  Next Obligation. rewrite <- H0. now rewrite <- H1. Qed.
  Next Obligation. now exists x. Qed.

  Definition comp (f g: mon): mon :=
    {|
      body := fun x => f (g x);
      Hbody x y H := Hbody f _ _ (Hbody g _ _ H)
    |}.
  Infix "°" := comp (at level 20): CPO.
  Program Definition comp_prop (f g: mon_prop) (Hf : is_correct f): mon_prop :=
    {|
      body_prop x y := exists2 z, g x z & f z y;
    |}.
  Next Obligation. apply Hbody_prop with f H0 H1; try assumption. now apply Hbody_prop with g x y. Qed.
  Next Obligation. destruct (Hfun g x) as [z [Hgz Hz]]. destruct (Hfun f z) as [y [Hfy Hy]]. 
    exists y. split. now exists z. intro y'. split. intro Hz'. destruct Hz' as [z' Hgz' Hfz'].
    apply Hy. apply Hf with z'. now rewrite <- (Hz z'). assumption.
    intro. exists z. assumption. now apply Hy.
  Qed.

  (* Iterations of a function *)

  Fixpoint itere F n x0 : X :=
    match n with
    | 0 => x0
    | S m => F (itere F m x0)
    end. (*Indexed by n for simplicity on comparison properties.*)
  
  #[global] Instance Hbody_itere (F:mon) n : Proper (weq ==> weq) (itere F n).
  Proof. 
  induction n. cbn. apply (op_leq_weq_1 (Hf:=(Hbody id))). cbn. 
  intros x y Hxy. apply weq_spec. split; apply Hbody; apply weq_spec; now apply IHn.
  Qed.

  Lemma itere_monotony (F:mon) : forall n, Proper (leq ==> leq) (itere F n).
  Proof. intros n x y H. induction n. now cbn. cbn. now apply Hbody. Qed.

  Lemma chain_itere (F:mon) bot : is_bot bot -> forall (n : nat), itere F n bot <= itere F (S n) bot.
  Proof. intros Hbot n. induction n. cbn. now apply bot_spec. cbn. now apply Hbody. Qed.

  Lemma chain_increase (F:mon) bot : is_bot bot -> forall (m n : nat), le n m -> itere F n bot <= itere F m bot.
  Proof.
    intros Hbot m n H. induction m. now inversion H.
    inversion H. easy.
    rewrite <- chain_itere. now apply IHm. assumption.
  Qed.

  Lemma itere_preserves_fix (F:mon) : forall β n, Fix F β -> (itere F n β) == β.
  Proof.
    intros. induction n. now cbn. cbn. unfold Fix in H. rewrite <- H at 2.
    now apply Hbody'.
  Qed.

  Variant iteres F : X -> Prop :=
  | from_bot : forall n bot, is_bot bot -> iteres F (itere F n bot).

  Lemma iteres_directed (F:mon): Directed leq (iteres F).
  Proof.
    unfold Directed. intros. destruct H as [n bot1 Hbot1]. destruct H0 as [m bot2 Hbot2].
    assert (bot1 == bot2). now apply (sup_unicity empty).
      setoid_rewrite H.
    destruct le_ge_dec with n m.
    + exists (itere F m bot2). repeat split. assumption. now apply chain_increase.
       reflexivity.
    + exists (itere F n bot2). repeat split; intuition. now apply chain_increase.
  Qed.

  Variant iteres_from_1 F : X -> Prop :=
  | from_bot_from_1 : forall n bot, is_bot bot -> le 1 n -> iteres_from_1 F (itere F n bot).

  Lemma iteres_from_1_directed (F:mon): Directed leq (iteres_from_1 F).
  Proof.
    unfold Directed. intros. destruct H as [n bot1 Hbot1]. destruct H0 as [m bot2 Hbot2].
    assert (bot1 == bot2). now apply (sup_unicity empty).
      setoid_rewrite H1.
    destruct le_ge_dec with n m.
    + exists (itere F m bot2). repeat split; try assumption. now apply chain_increase. reflexivity.
    + exists (itere F n bot2). repeat split; try assumption. reflexivity. now apply chain_increase.
  Qed.

  Lemma image_of_iteres F : set_eq (Image F (iteres F)) (iteres_from_1 F).
  Proof.
    intro. split; intro; inversion H. inversion H0.
    + assert (iteres_from_1 F (itere F (S n) bot)). apply from_bot_from_1. assumption. lia.
      apply H4.
    + induction n. contradict H0. lia.
      cbn. apply from_image. apply from_bot. assumption.
  Qed.

  Lemma from_1_included F : included (iteres_from_1 F) (iteres F).
  Proof. intros x H. inversion H. apply from_bot. assumption. Qed.

End functions.

Section Particular_CPOs.

  Context {X} {P' : PO X} {P: CPO P'}.

(*
 Program Instance PO_mon : PO mon :=
    {|
      weq := pointwise_relation X weq;
      leq := pointwise_relation X leq;
    |}.
  Next Obligation.
  apply Build_PreOrder.
    + intro x. reflexivity.
    + intros f g h Hfg Hgh x. now transitivity (g x).
  Qed.
  Next Obligation.
    split; intros.
    + split; intro a; now apply weq_spec.
    + intro. now apply weq_spec.
  Qed.
*)

 Program Instance PO_mon_prop : PO mon_prop :=
    {|
      weq f g := forall x yf yg, f x yf -> g x yg -> yf == yg;
      leq f g := forall x, forall yf yg, f x yf -> g x yg ->  yf <= yg;
    |}.
  Next Obligation.
  apply Build_PreOrder.
    + intros f x y1 y2 Hy1 Hy2. destruct (Hfun f x). apply H in Hy1, Hy2. now rewrite <- Hy1, Hy2.
    + intros f g h Hfg Hgh x yf yh Hyf Hyh. destruct (Hfun g x) as [yg [Hyg _]]. transitivity yg.
      now apply (Hfg x). now apply (Hgh x).
  Qed.
  Next Obligation.
    split; intros.
    + split; intros d ix iy Hix Hiy. rewrite (H d ix iy); intuition. rewrite (H d iy ix); intuition.
    + destruct H as [Hinf1 Hinf2]. apply weq_spec. split. now apply (Hinf1 x0). now apply (Hinf2 x0).
  Qed.

  
  Program Definition sup_mon (F : directed_set leq) (H : forall (x:X), Directed (@leq X P') (fun z => exists2 g, F g & g x z)) := 
  {| body_prop (x y : X) := @sup X P' P (fun (z:X) => exists2 g, F g & g x z) y |}.
  Next Obligation.
    eapply sup_spec. apply H1. cbn. intros zgx [g Hzgx]. destruct (Hfun g y) as [zgy [Hzgy Hgy]].
    transitivity zgy. now apply Hbody_prop with g x y.
    apply (leq_xsup (exist (fun Dbody : set X => Directed leq Dbody)
          (fun z : X => exists2 g : mon_prop, F g & g y z)
          (sup_mon_obligation_1 F H y))). cbn. now exists g. assumption.
  Qed.
  Next Obligation.
    destruct (sup_exists (exist (fun Dbody0 : set X => Directed leq Dbody0)
       (fun z : X => exists2 g : mon_prop, F g & g x z)
       (sup_mon_obligation_1 F H x))) as [y Hy].
    exists y. split. assumption. intro. split. intro Hy'.
    + eapply sup_unicity. apply Hy. eapply sup_is_independent_of_proof. 2: apply Hy'. cbn. intro. reflexivity.
    + intro Hyy'. apply sup_spec. intro z. transitivity (y <= z). split; intro. now rewrite Hyy'. now rewrite <- Hyy'.
      now apply sup_spec.
Qed.

  Lemma directed_funs_implies_directed_sets F : Directed (@leq mon_prop PO_mon_prop) F
  -> (forall (x:X), Directed (@leq X P') (fun z => exists2 g, F g & g x z)).
  Proof.
    intro D. unfold Directed. intros.
      destruct H as [fx Hfx]. destruct H0 as [fy Hfy].
      destruct (D fx fy) as [g [Hg1S [Hgf1 Hgf2]]]; try assumption.
      destruct (Hfun g x) as [yg [Hyg _]].
      exists (yg). repeat split. now exists g.
                                   now apply (Hgf1 x).
                                   now apply (Hgf2 x).
  Qed.

  Program Instance CPO_mon_prop : CPO PO_mon_prop :=
    {|
      sup F f := forall x y, f x y <-> @sup X P' P (fun z => exists2 g, F g & g x z) y ;
    |}.
  (* Now brace yourself, these manipulations are complexe and ugly for what they say... *)
  Next Obligation. apply directed_funs_implies_directed_sets. now destruct F. Qed.
  Next Obligation.
    assert (forall (x:X), Directed (@leq X P') (fun z => exists2 g, D g & g x z)) as Di.
      apply directed_funs_implies_directed_sets. now destruct D.
    split.
    + intros. split. 
      - intros Hdz f HDf x yf yz Hyf Hyz. destruct (Hfun d x) as [yd [Hyd Hd]].
        transitivity yd. apply (leq_xsup (exist (fun Dbody : set X => Directed leq Dbody)
             (fun z : X => exists2 g : mon_prop, D g & g x z)
             (CPO_mon_prop_obligation_1 D x))). cbn. now exists f. now apply H.
        now apply Hdz with x.
      - intros Hyz x yd yz Hdy Hzy. eapply sup_spec. now apply (H x yd). cbn. intros.
        destruct H0 as [g HDg Hgy]. now apply (Hyz g HDg x).
    + intros. transitivity (sup_mon D Di x y).
      - split. intro Hdy. cbn. rewrite sup_spec. cbn. intros. split; intros.
        * transitivity y; try assumption. destruct (H d). destruct H1 as [f ? ?]. apply H2 with f x; intuition.
          destruct (Hfun d x0) as [yd [? ?]]. apply weq_spec. transitivity yd. symmetry.
          now rewrite <- (H8 yg). now rewrite <- (H8 yf).
        * destruct (Hfun (sup_mon D Di) x) as [y' [HDy' Hy']]. transitivity y'.
          ** destruct (H (sup_mon D Di)) as [_ HDy]. apply HDy with x; try assumption.
            intros f HDf x0 yf0 yD0 Hf0 HD0. cbn in HD0.
            apply (leq_xsup (exist (fun Dbody : set X => Directed leq Dbody)
            (fun z : X => exists2 g : mon_prop, D g & g x0 z)
            (sup_mon_obligation_1 D Di x0))). cbn. now exists f. assumption.
          ** eapply sup_spec. apply HDy'. now cbn.
        * intro HDy. destruct (Hfun d x) as [yd [Hdyd Hyd]]. apply Hbody_prop' with yd; try assumption.
          apply weq_spec. split.
          ** eapply sup_spec. apply HDy. cbn. intros yf [f Hyf]. destruct (H d) as [Hd _].
            apply Hd with f x; try assumption. intros x0 yd1 yd2 Hd1 Hd2. destruct (Hfun d x0) as [yd0 [Hyd0 Hd0]].
            apply weq_spec. transitivity yd0. symmetry. now rewrite <- (Hd0 yd2). now rewrite <- (Hd0 yd1).
          ** destruct (H (sup_mon D Di)) as [_ HD]. apply HD with x; try assumption. intros f HDf x0 yf0 yD0 Hf0 HD0.
            cbn in HD0. apply (leq_xsup (exist (fun Dbody : set X => Directed leq Dbody)
            (fun z : X => exists2 g : mon_prop, D g & g x0 z)
            (sup_mon_obligation_1 D Di x0))). cbn. now exists f. assumption.
      - apply sup_is_independent_of_proof. cbn. intro. reflexivity.
Qed.
  Next Obligation.
    assert (forall (x:X), Directed (@leq X P') (fun z => exists2 g, D g & g x z)) as Di.
      apply directed_funs_implies_directed_sets. now destruct D.
    exists (sup_mon D Di). intros x y. apply sup_is_independent_of_proof. cbn.
    intro. reflexivity.
Qed.

  Program Instance PO_parts: PO (set X) :=
    {|
      weq := set_eq;
      leq := included;
    |}.
  Next Obligation.
    apply Build_PreOrder.
    + intro Y. now intro x.
    + apply Included_trans.
  Qed.
  Next Obligation.
    repeat split; try intuition; intros a; intro H0; apply H; try apply H0.
  Qed.

(* Still need that ? *)
(*
  Program Instance CPO_parts: CPO PO_parts :=
    {|
      sup A := (fun x => exists Y, A Y /\ Y x);
    |}.
  
  Next Obligation.
    split; intros; intros a Ha.
    apply H. now exists y.
    destruct Ha. apply (H x). apply H0. apply H0.
  Qed.

  Program Instance Lattice_parts : CompleteLattice (PO_parts) :=
    {|
      supL A := (fun x => exists Y, A Y /\ Y x);
    |}.
  Next Obligation.
    split; intros; intros a Ha. apply H.
    now exists y.
    destruct Ha. apply (H x). apply H0. apply H0.
  Qed.
*)


  (** * sub-CPO : Define a set (part of X) as being a CPO *)

  Definition is_subCPO (Y : set X) := forall (D : directed_set _),
      included D Y -> exists y, Y y /\ (sup D y).

  Definition down (x:X) := (fun z => z <= x).

  Lemma down_is_subCPO : forall x, is_subCPO (down x).
  Proof. intros x D Hd. unfold down. destruct (sup_exists (CPO := P)) with D as [y Hy].
    exists y. split; try assumption. eapply sup_spec. apply Hy. intros. now apply Hd. Qed.

  Definition set_type (Y : set X) : Type := { x : X | Y x}.
  Definition element Y (y :set_type Y) := proj1_sig y.
  #[global] Coercion element : set_type >-> X.

  Definition complete_body {Y : set X} (D : set (set_type Y)) : set X :=
    (fun x => {is_in_Y : Y x & D (exist _ x is_in_Y)}).
  
  Lemma is_in_complete {Y: set X} (D : set (set_type Y)) : forall y, D y -> complete_body D (element y).
  Proof. intros. destruct y. unfold complete_body. cbn. exists y. apply H. Qed.
  
  Program Instance subPO (Y:set X) : (PO (set_type Y)) :=
    {|
      weq x y := (@weq X P') x y;
      leq x y := (@leq X P') x y;
    |}.
  Next Obligation. apply Build_PreOrder; intro x. reflexivity. intros y z Hxy Hyz. now transitivity (element y). Qed.
  Next Obligation. apply weq_spec. Qed.

  Program Instance subCPO (Y:set X) (H : is_subCPO Y) : (CPO (subPO Y)) :=
    {|
      sup D := sup (exist (Directed (@leq X P')) (complete_body D) _) ;
    |}.
  Next Obligation.
    destruct D as [D Hd]. cbn. intros x y Hx Hy. inversion Hx. inversion Hy.
    destruct (Hd (exist (fun x : X => Y x) x x0) (exist (fun x : X => Y x) y x1))
      as [[z Pz] [Hz [Hxz Hyz]]]; try assumption.
    exists z. split. now exists Pz. now split.
  Qed.
  Next Obligation.
    split.
    + intros. split. intros. transitivity d. eapply leq_xsup.
    2 : apply H0. cbn. now apply is_in_complete. assumption.
     intro Hz. eapply sup_spec. apply H0. intros x Hx. cbn in Hx. destruct Hx as [Px Dx].
     now apply (Hz (exist (fun x : X => Y x) x Px)).
    + intros. apply sup_spec. intros. split. intros Hdz x Hx. transitivity d. cbn in Hx.
      destruct Hx as [Px Dx]. cut ((exist (fun x : X => Y x) x Px) <= d). intro Hr. apply Hr.
      apply (H0 d); intuition. assumption.
      (* Need to build things to use is_subCPO Y. *)
      intros. destruct D as [D Hd]; cbn in *. assert (Directed leq (complete_body D)).
        intros x y Hx Hy. inversion Hx. inversion Hy.
        destruct (Hd (exist (fun x : X => Y x) x x0) (exist (fun x : X => Y x) y x1))
          as [[z' Pz'] [Hz' [Hxz' Hyz']]]; try assumption.
        exists z'. split. now exists Pz'. now split.
      destruct (H (exist (Directed (@leq X P')) (complete_body D) H2)). cbn. intros x Hx.
      destruct Hx as [Px Dx]. assumption. destruct H3.
      transitivity x. destruct (H0 (exist _ x H3)) as [_ HH]. apply HH. intros.
      cbn. eapply leq_xsup. 2: apply H4. cbn. now apply is_in_complete.
      eapply sup_spec. apply H4. apply H1.
  Qed.
  Next Obligation.
    destruct D as [D Hd]; cbn in *. assert (Directed leq (complete_body D)).
        intros x y Hx Hy. inversion Hx. inversion Hy.
        destruct (Hd (exist (fun x : X => Y x) x x0) (exist (fun x : X => Y x) y x1))
          as [[z' Pz'] [Hz' [Hxz' Hyz']]]; try assumption.
        exists z'. split. now exists Pz'. now split.
    destruct (H (exist (Directed (@leq X P')) (complete_body D) H0)). cbn. intros x Hx.
      destruct Hx as [Px Dx]. assumption. destruct H1.
    exists (exist _ x H1). apply (sup_is_independent_of_proof (exist (Directed leq) (complete_body D) H0)).
    cbn. intro. reflexivity. apply H2.
  Qed.

  (* Some instances that can now be defined on CPO_parts and CPO_mon. *)

  Variable F : X -> X.

  #[global] Instance image_eq : Proper (weq ==> weq) (Image F).
  Proof. intros Y1 Y2 HY. split; intro H; inversion H; apply from_image; now apply HY. Qed.

  #[global] Instance set_incl : Proper (weq ==> weq ==> iff) included.
  Proof. intros Y1 Y2 H12 Y3 Y4 H34. split; intros Hi x Hx; apply H34; apply Hi; now apply H12. Qed.

  Lemma set_equivalent : forall (f g : set X), f == g -> (pointwise_relation X iff) f g.
  Proof.
    intros f g H x. split; intro Hh; apply weq_spec in H; destruct H.
    now apply H. now apply H0.
  Qed.

End Particular_CPOs.

Ltac rew H H' :=
  let eq := fresh in
  pose proof @set_equivalent _ _ H as eq;
  apply eq in H';
  clear eq.

Ltac rew_goal H :=
  let eq := fresh in
  pose proof @set_equivalent _ _ H as eq;
  apply eq;
  clear eq.

Tactic Notation "prew" hyp(H) "in" hyp(H') := rew H H'.
Tactic Notation "prew" constr(H) "in" hyp(H') := rew H H'.
Tactic Notation "prew" hyp(H)    := rew_goal H.
Tactic Notation "prew" constr(H) := rew_goal H.

(** * Common fixpoint of every monotonous increasing function *)

Section Increasing_fixpoint.
    Context {X} `{P: CPO X}.

  Definition Increasing F := forall x, x <= F x.
  Definition Increasing_prop F := forall x y, F x y -> x <= y.

  Definition leq_mon := (@leq mon_prop PO_mon_prop).
  Definition weq_mon := (@weq mon_prop PO_mon_prop).
 
  Definition correct := forall (f:mon_prop), is_correct f.

  Program Definition Increasing_functions (c : correct) := exist (Directed leq_mon) Increasing_prop _.
  Next Obligation.
    unfold Directed. intros f g Hf Hg. exists (comp_prop g (c f)). repeat split.
    + intros x y Hgfxy. destruct Hgfxy. transitivity x0. now apply Hg. now apply Hf.
    + intros x yf yfg Hyf Hyfg. destruct (Hyfg). apply Hbody_prop with f x x0; try assumption. apply Hg. now apply H.
    + intros x yg yfg Hyg Hyfg. destruct Hyfg. apply Hf. apply (c f) with x0. destruct (Hfun g x) as [yg0 [Hy0 Hg0]].
      transitivity yg0. symmetry. now rewrite <- Hg0. now apply Hg0. assumption.
  Defined.

  Lemma exists_fixpoint_of_all_Increasing (c : correct): exists mu, forall (f : mon_prop), Increasing_prop f -> Fix_prop f mu.
  Proof.
    destruct ((sup_exists (CPO := CPO_mon_prop)) (Increasing_functions c)) as [Hsup HHsup].
    destruct (sup_exists empty) as [bot Hbot]. destruct (Hfun Hsup bot) as [mu [Hbotmu Hmu]].
    exists mu. intros f Hf. unfold Fix_prop. destruct (Hfun f mu) as [ymu [Hfymu Hymu]]. apply Hymu.
    apply weq_spec. split.
     + assert (Increasing_prop Hsup).
         intros x y Hsxy. assert (leq_mon id_prop Hsup). eapply leq_xsup. 2: apply HHsup. intros z yz Hyz.
         now apply weq_spec. apply (H x); now cbn.
       eapply leq_xsup. 2 : apply HHsup. cbn. 2 : apply Hbotmu.
       exists (comp_prop Hsup (c f)). intros x y Hcxy. destruct Hcxy. transitivity x0. now apply H. now apply Hf.
       now exists mu.
     + now apply Hf.
  Qed.
  
  Lemma increasing_has_fix_point (F:mon_prop) (c : correct) : Increasing_prop F -> exists x, Fix_prop F x.
  Proof. intro HF. destruct (exists_fixpoint_of_all_Increasing c) as [mu ?]. exists mu. now apply H. Qed.

(*
  Definition H_sup := (sup (CPO := CPO_mon) Increasing_functions).
  
  Lemma H_sup_is_increasing : Increasing H_sup.
  Proof. intro. assert (leq_mon id H_sup). now apply (sup_spec (CPO := CPO_mon) Increasing_functions). apply H. Qed.

  Lemma H_sup_bot_is_fixpoint_of_all_Increasing (F:mon) :
    Increasing F -> Fix F (H_sup bot).
  Proof.
    intro. assert (weq_mon (comp F H_sup) H_sup).
    + apply weq_spec. split. apply (sup_spec (CPO := CPO_mon) Increasing_functions). reflexivity.
      intro x. transitivity (H_sup x). apply H_sup_is_increasing. apply H.
      intro. apply H.
    + unfold Fix. now setoid_rewrite (H0 bot).
  Qed.

  (* Lemma 8.21*)
  Lemma increasing_has_fix_point (F:mon) : Increasing F -> exists x, Fix F x.
  Proof.
    intro. exists (H_sup bot). now apply H_sup_bot_is_fixpoint_of_all_Increasing.
  Qed.
*)
End Increasing_fixpoint.


(** * Invariant subCPOs *)

Section Invariant_subCPOs.

  Context {X} `{P: CPO X}.

  Definition Invariant (F : X -> X) Y := included (Image F Y) Y.

  Variable F : X -> X.

  Definition P0 :=  (*P0 is the smallest invariant subCPO : intersection of all invariant sub_CPOs.*)
    (fun x => forall Y, Invariant F Y -> is_subCPO Y -> Y x).
    
  Definition correct_set := forall (Y : set X), Proper (weq ==> iff) Y.

  Lemma P0_is_invariant_subCPO (c : correct_set) : Invariant F P0 /\ is_subCPO P0.
  Proof.
    split.
    + intros x H. inversion H. intros Y Hi Hs. apply Hi. apply from_image. now apply (H0 Y).
    + intros D H. destruct (sup_exists D) as [d Hd]. exists d. split; try assumption.
      intros Y Hy Hs. destruct (Hs D). transitivity P0. assumption. intros x Hx. now apply (Hx Y).
      destruct H0. apply (c Y) with x; try assumption. eapply sup_unicity. apply Hd. assumption.
  Qed.

  Lemma P0_is_smallest_invariant_subCPO : forall Y, Invariant F Y -> is_subCPO Y -> included P0 Y.
  Proof. intros Y Hi Hs x Hx. now apply Hx. Qed.

End Invariant_subCPOs.


(* Knaster-Tarski Theorem on Lattices *)
(*
Section lattice_results.
  Context {X} `{L: CompleteLattice X}.
  Variable b: mon.

  Definition gfp := supL (fun x => x <= b x).
  Definition lfp := inf_lat (fun x => b x <= x).

  Proposition leq_gfp: forall y, y <= b y -> y <= gfp.
  Proof. apply leq_xsupL. Qed.
  Proposition geq_lfp: forall y, b y <= y -> lfp <= y.
  Proof. apply leq_xinf. Qed.

  Lemma gfp_pfp: gfp <= b gfp.
  Proof.
    unfold gfp. apply sup_specL. intros y H. rewrite H. apply Hbody.
    apply leq_xsupL. apply H.
  Qed.
  Lemma lfp_pfp: b lfp <= lfp.
  Proof.
    unfold lfp. apply inf_spec_lat. intros y H. rewrite <- H. apply Hbody.
    apply leq_xinf. apply H.
  Qed.

  Lemma gfp_fp: gfp == b gfp.
  Proof.
    rewrite weq_spec. split.
    + apply gfp_pfp.
    + apply leq_xsupL. apply Hbody. apply gfp_pfp.
  Qed.
  Lemma lfp_fp: lfp == b lfp.
  Proof.
    rewrite weq_spec. split.
    + apply leq_xinf. apply Hbody. apply lfp_pfp.
    + apply lfp_pfp.
  Qed.
End lattice_results.
*)

Section Using_Tarski.
  (* Remark : although this section is used in the proofs of the book, it is not used throughout this file.
It is enough to work with P0 as the smallest invariant subCPO, no need to use its properties of least fixpoint. *)

(*
  Context {X} `{P: CPO X}.

  Program Definition Φ F' : @mon (set X) (PO_parts) :=  (*since def of mon is linked to that of POs, need a PO of parts*)
    {| body X := (fun x =>
                    (x = bot \/
                     (Image F' X) x \/
                       (exists (D : directed_set _), included (Dbody D) X /\ x = sup D)
                 ))
    |}.
  Next Obligation.
    intros Y1 Y2 H12 x Hx. destruct Hx; intuition.
    + right. left. inversion H0. apply from_image. now apply H12.
    + destruct H0 as [Hd [Hi Hs]]. right. right. exists Hd. split.
      intros y Hy. apply H12. now apply Hi. assumption.
  Qed.

  Definition P0' F' := lfp (L := Lattice_parts) (Φ F').

  Lemma P0_is_P0' F : set_eq (P0 F) (P0' F).
  Proof.
    split.
    + apply P0_is_smallest_invariant_subCPO.
    - unfold Invariant. unfold P0'. rewrite lfp_fp at 2.
      intros x H. right. now left.
    - unfold is_subCPO. unfold P0'. intros D H.
      apply (set_equivalent (lfp_fp (Φ F))). (* prew does not work *)
      right. right. now exists D.
                          + unfold P0'. apply (geq_lfp (L := Lattice_parts)). intros x H.
                            destruct (P0_is_invariant_subCPO F). destruct H. rewrite H.
                            apply (H1 empty). intros y Hy. contradict Hy.
                            destruct H. inversion H. apply H0. now apply from_image.
                            destruct H as [D [Hd Hs]]. rewrite Hs. now apply (H1 D).
  Qed.
*)
End Using_Tarski.


(** * Fixpoint theorems ! *)

Section Fixpoints.
  Context {X} `{P: CPO X}.

  Definition is_least S x := S x /\ forall y, S y -> x <= y.
  Definition is_inf S x := forall z, (forall y, S y -> z <= y) <-> z <= x.
  Definition is_minimal S x := S x /\ forall y, S y -> y <= x -> y == x.
  Definition is_greatest S x := S x /\ forall y, S y -> y <= x.
  Definition is_sup S x := forall z, (forall y, S y -> y <= z) <-> x <= z.

(*
  Lemma test_coherence1 : forall (D : directed_set _), is_sup D (sup D).
  Proof. intros D z. split; apply sup_spec. Qed.
  Lemma test_coherence2 : forall (D : directed_set _),
      D (sup D) ->
      is_greatest D (sup D).
  Proof. intros. split. assumption. now apply sup_spec. Qed.
*)

  (** * Fixpoint theorems and proofs : first theorem. *)
  Variable F:mon.

  Program Definition sup_Chain := (sup (exist _ (iteres F) (iteres_directed F))).

  Theorem Fixpoint_I_i : forall α, sup_Chain α -> Fix F α -> is_least (Fix F) α.
  Proof.
    intros α Hα HFα. split; try assumption.
    intros. eapply sup_spec. apply Hα. cbn. intros z Q.
    inversion Q. rewrite <- (itere_preserves_fix F y n).
    apply itere_monotony. now apply bot_spec. assumption.
  Qed.

  Program Definition sup_Chain' := (sup (exist _ (iteres_from_1 F) _)).
  Next Obligation. apply iteres_from_1_directed. Qed.

  Lemma sup_from_1 : forall α α', sup_Chain α -> sup_Chain' α' -> α == α'.
  Proof.
    intros α α' Hα Hα'. apply weq_spec. split.
    + eapply sup_spec. apply Hα. cbn. intros. inversion H.
      induction n. cbn. now apply bot_spec. eapply leq_xsup. 2: apply Hα'. apply from_bot_from_1. assumption. lia.
    + eapply sup_preserves_inclusion; cbn. 2 : apply Hα'. 2 : apply Hα. apply from_1_included.
  Qed.

  Theorem Fixpoint_I_ii : Continuous F -> exists α, is_least (Fix F) α. (* Note that F is monotonous too. *)
  Proof.
    intro H. destruct (sup_exists (exist _ (iteres F) (iteres_directed F))) as [α Hα]. exists α.
    destruct (sup_exists ((exist _ (iteres_from_1 F) (iteres_from_1_directed F)))) as [α' Hα'].
    assert (Fix F α).
    + unfold Fix. destruct (H (iteres F) (iteres_directed F)) as [HD HS].
      transitivity α'; try now rewrite sup_from_1. rewrite HS. reflexivity. assumption.
      eapply sup_is_independent_of_proof. 2: apply Hα'. cbn. unfold set_eq. apply image_of_iteres.
      symmetry. apply sup_from_1. apply Hα. eapply sup_is_independent_of_proof. 2: apply Hα'. 
      cbn. intro. reflexivity.
    + now apply Fixpoint_I_i.
  Qed.

  (** * Fixpoint theorems and proofs : second theorem. *)

  Lemma Induction_Rule : (exists µ0, is_least (Pre F) µ0)
                         -> exists µ, is_least (Fix F) µ /\ forall x, Pre F x -> µ <= x.
  Proof.
    intro H. destruct H as [µ0 Hmu0].
    exists µ0. repeat split.
    + apply weq_spec. split. apply Hmu0.
      apply Hmu0. unfold Pre. apply Hbody. apply Hmu0.
    + intros. apply Hmu0. now apply fix_is_pre.
    + apply Hmu0.
  Qed.

  Lemma P0_is_in_Post (c : correct_set) : included (P0 F) (Post F).
  Proof.
    assert (Invariant F (Post F) /\ is_subCPO (Post F)).
    + split.
    - intros x H. inversion H. apply Hbody. apply H0.
    - intros D H. destruct (sup_exists D) as [d Hd]. exists d. split; try assumption.
      eapply sup_spec. apply Hd. intros. transitivity (F y). now apply H.
      apply Hbody. now apply leq_xsup with D.
      + now apply P0_is_smallest_invariant_subCPO.
  Qed.
  (* Note : contrarily to the book, here P0' was never used for now, neither was phi. *)

  Lemma P0_is_in_down x : Fix F x -> included (P0 F) (down x).
  Proof.
    intro. assert (Invariant F (down x) /\ is_subCPO (down x)).
    + split.
    - intros y Hy. inversion Hy. unfold down. rewrite <- H. apply Hbody. apply H0.
    - apply down_is_subCPO.
      + now apply P0_is_smallest_invariant_subCPO.
  Qed.

  Program Instance P0_PO : PO (set_type (P0 F)) := (subPO _).
  Program Instance P0_CPO (c : correct_set (X := X)) : CPO P0_PO := (subCPO _).
  Next Obligation. apply P0_is_invariant_subCPO. assumption. Qed.

  Program Definition F_restricted_to_P0 (c : correct_set (X := X)) : mon :=
    {| body := fun y => (exist _ (F y) _) |}.
  Next Obligation. destruct y as [x Hx]; cbn. apply P0_is_invariant_subCPO. assumption. now apply from_image. Qed.
  Next Obligation. intros y1 y2 H12; cbn. now apply Hbody. Qed.

  Lemma F_restricted_is_increasing (c : correct_set (X := X)) : Increasing (F_restricted_to_P0 c).
  Proof. intro y. destruct y as [x Hx]; cbn. now apply P0_is_in_Post. Qed.
  
  Lemma F_prop_still_increasing {Y} {PY : PO Y} (G:@mon Y PY): Increasing G -> Increasing_prop (from_mon G).
  Proof. intros H x y HGxy. cbn in HGxy. rewrite HGxy. apply H. Qed.

  Lemma F_prop_restricted_is_increasing (c : correct_set (X := X)) : Increasing_prop (from_mon (F_restricted_to_P0 c)).
  Proof. apply (F_prop_still_increasing (F_restricted_to_P0 c) (F_restricted_is_increasing c)). Qed.

  Theorem Fixpoint_II (c : correct_set (X := X)) (c' : correct) : exists x, Fix F x.
  Proof.
    destruct (increasing_has_fix_point (P := P0_CPO c) (from_mon (F_restricted_to_P0 c)) c' (F_prop_restricted_is_increasing c)).
    destruct x as [x Hx]. cbn in H. exists x. unfold Fix. symmetry. apply H.
  Qed.
  
  (* Actually, we can go further. Since we constructively built the fixpoint of G as being (H_sup bot) for a well-chosen CPO.
 So we can define this fixpoint and add the results from Claim 3 of the theorem : it is both the top of P0 and the least fixpoint of F.*)

  Theorem exists_top_of_P0_and_least_fixpoint_of_F (c : correct_set (X := X)) (c' : correct):
    exists (a : set_type (P0 F)), is_greatest (P0 F) (element a) /\ is_least (Fix F) (element a).
  Proof.
  destruct (increasing_has_fix_point (P := P0_CPO c) (from_mon (F_restricted_to_P0 c)) c' (F_prop_restricted_is_increasing c)) as [a ?].
    destruct a as [a Ha]. cbn in H. exists (exist _ a Ha).
   split.
         + split. now cbn. apply P0_is_in_down.
           intros. cbn. unfold Fix. now symmetry.
         + split. cbn. unfold Fix. now symmetry. intros. apply (P0_is_in_down y).
           assumption. now cbn.
  Qed.

End Fixpoints.


(** * Theorem III : Bourbaki-Witt theorem. This theorem requires classic logic, it is false in intuitionist logic. *)

Section Bourbaki_Witt.

  Context {X} `{P: CPO X}.
  Definition classic_axiom := forall (P : Prop), P \/ ~ P.

  (* Now show that P0 is a chain, to prove that it has a sup (top). This is a fixpoint. *)

  Definition lt x y := x <= y /\ ~ (x == y).
  Infix "<" := lt.

  Lemma leq_is_lt_or_eq : classic_axiom -> forall x y, x <= y -> x==y \/ x < y. (* excluded middle ! *)
  Proof. intros EM x y Hxy. destruct (EM (x==y)). now left. now right. Qed.

  Lemma not_leq_and_gt : forall x y, ~ (x <= y /\ y < x). (* no need for EM *)
  Proof. intros x y. intro. destruct H. destruct H0. contradict H1. now apply weq_spec. Qed.
  
  Lemma lt_preserves_eq : forall x y z, x==y -> (z < x <-> z < y).
  Proof. intros x y z Hxy. split; intro H. split; rewrite <- Hxy; apply H.
    split; rewrite Hxy; apply H. Qed.
    
  Lemma lt_leq_transitivity : forall x y z, x < y -> y <= z -> x < z.
  Proof. intros x y z Hxy Hyz. split. transitivity y. apply Hxy. assumption.
    intro. assert (x == y). apply weq_spec. split. apply Hxy. now rewrite H. destruct Hxy.
    contradiction.
  Qed.

  Definition Extreme F' : set X :=
    (fun c => (P0 F') c /\ forall x, (P0 F') x -> x < c -> F' x <= c).

  Definition Mc F' c : set X :=
    (fun x => (P0 F') x /\ (x <= c \/ F' c <= x)).

  Lemma Mc_is_P0 F' (C : correct_set) : classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> forall c, Extreme F' c -> set_eq (P0 F') (Mc F' c).
  Proof.
    intros EM Fp HF c Ec. destruct Ec as [Pc Ec']. split.
    + apply P0_is_smallest_invariant_subCPO.
    - intros x Hx. inversion Hx. split. apply P0_is_invariant_subCPO. apply C. apply from_image. apply H.
      destruct H as [Px0 Hx0]. destruct Hx0.
      * apply leq_is_lt_or_eq in H. destruct H. right. apply weq_spec. now apply Fp.
        left. now apply Ec'. assumption.
      * right. transitivity x0. assumption. apply HF.
    - intros D Hi. destruct (sup_exists D) as [d Hd]. exists d. split; try assumption.
      destruct P0_is_invariant_subCPO with F'. apply C. destruct H0 with D. rewrite Hi. intros x0 Hx0. apply Hx0.
      split. apply (C (P0 F')) with x. now apply sup_unicity with D. apply H1.
      destruct (EM (exists y, D y /\ F' c <= y)). (* WARNING : excluded middle ! *)
      * right. destruct H2 as [y Hy]. transitivity y. apply Hy. now apply leq_xsup with D.
      * left. eapply sup_spec. apply Hd. intros. destruct (Hi y). assumption.
        destruct H5. assumption. contradict H2. now exists y.
                                                     + intro Hm. apply Hm.
  Qed.

  Lemma P0_is_extreme F' (C : correct_set) : classic_axiom -> (Proper (weq ==> weq) F') ->  Increasing F' -> forall x, P0 F' x -> Extreme F' x.
  Proof.
    intros EM Fp HF. apply P0_is_smallest_invariant_subCPO.
    + intros c Hc. inversion Hc. inversion H as [HPx HEx]. split.
    - apply P0_is_invariant_subCPO. apply C. now apply from_image.
    - intros. assert (set_eq (P0 F') (Mc F' x)). apply (Mc_is_P0 C EM Fp HF H).
      assert (Mc F' x x0). now rewrite <- (set_equivalent H3 x0). destruct H4. destruct H5.
      * apply leq_is_lt_or_eq in H5; intuition.
        apply weq_spec. now apply Fp. transitivity x; intuition.
      * exfalso. eapply not_leq_and_gt. split. apply H5. apply H2.
      + intros D Ed. destruct (sup_exists D) as [d Hd]. exists d. split; try assumption.
      destruct P0_is_invariant_subCPO with F'. apply C. destruct H0 with D. rewrite Ed. intros x0 Hx0. apply Hx0.
      split. apply (C (P0 F')) with x. now apply sup_unicity with D. apply H1.
        intros x0 Px0 Hx0d. destruct (EM (exists c, D c /\ x0 <= c)).
    - destruct H2 as [c [Hdc Hcx0]]. apply leq_is_lt_or_eq in Hcx0; intuition.
      * transitivity (F' c). apply weq_spec. now apply Fp.
        assert (Mc F' c x). apply Mc_is_P0; intuition. destruct P0_is_invariant_subCPO with F'. apply C.
          destruct H0 with D. rewrite Ed. intros z0 Hz0. apply Hz0.
        destruct H4. destruct H8. exfalso. eapply not_leq_and_gt. split. apply weq_spec. apply H1. 
        apply (lt_leq_transitivity c Hx0d). assert (d == x). now apply sup_unicity with D. 
        now rewrite H9. assert (d == x). now apply sup_unicity with D. now rewrite H9.
      * transitivity c. apply Ed; intuition. now apply leq_xsup with D.
    - assert (d <= x0).
      * eapply sup_spec. apply Hd. intros. rewrite HF. assert (Mc F' y x0). apply Mc_is_P0; intuition.
        destruct H4. destruct H5. contradict H2. exists y. now split. assumption.
      * exfalso. eapply not_leq_and_gt. split. apply H3. assumption.
  Qed.


  Lemma P0_is_Chain (F':X -> X) (C : correct_set): classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> is_Chain (P0 F').
  Proof.
    intros EM Fp HF x y Hx Hy. assert (Mc F' x y).
    apply Mc_is_P0; intuition. apply P0_is_extreme; intuition.
    destruct H. destruct H0. now right. left. transitivity (F' x).
    apply HF. assumption.
  Qed.

  Lemma P0_is_directed (F':X -> X) (C : correct_set) : classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> Directed leq (P0 F').
  Proof. intros EM Fp HF. apply chain_is_directed. now apply P0_is_Chain. Qed.

  (* Note : since we put excluded middle and functional extensionality as hypothesis, we lose constructivity,
we can't just define our fixpoint as below :
Program Definition top_P0 (F':X -> X) (H : Increasing F') := (sup (exist _ (P0 F') _)).
Next Obligation. apply P0_is_directed; intuition. apply H. Qed. *)

  (*The book is wrong : the top of P0 is not necessarily minimal (cf counterexample on paper)
However, from an existing fix point, it seems we can deduce a minimal fix point since the set of
fixpoints between bottom and our fix point is a chain. TODO ? *)
  Theorem Fixpoint_III (F' : X -> X) (C : correct_set) : classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> exists x, Fix F' x(*is_minimal (Fix F') x*).
  Proof.
    intros EM Fp HF. destruct (sup_exists (exist _ (P0 F') (P0_is_directed C EM Fp HF))) as [a Ha].
    exists a.
    apply weq_spec. split. eapply leq_xsup. 2: apply Ha. cbn. apply P0_is_invariant_subCPO. assumption.
    apply from_image. destruct P0_is_invariant_subCPO with F'. assumption.
    destruct H0 with (exist (Directed leq) (P0 F') (P0_is_directed C EM Fp HF)); cbn. now intro.
    apply (C (P0 F')) with x. eapply sup_unicity. apply Ha. apply H1. apply H1.
    eapply sup_spec. apply Ha. cbn. intros. rewrite <- HF. eapply leq_xsup. 2: apply Ha. now cbn.
  Qed.

End Bourbaki_Witt.



Section S_chain.

 Context {X} `{P: CPO X}.

 Inductive S F : X -> Prop :=
  | S_bot : forall x, is_bot x -> S F x
  | S_succ : forall x, S F x -> S F (F x)
  | S_sup : forall (D : directed_set leq) x, included D (S F) -> sup D x -> (S F) x.

 Lemma S_is_P0 (c : correct_set) : forall F, @weq (set X) PO_parts (S F) (P0 F).
 Proof.
 intro F. pose proof (P0_is_invariant_subCPO F c) as [Hi Hs]. apply antisym; cbn.
 + intros x HSx. induction HSx. 
   destruct (Hs empty). now intro. apply c with x0; intuition. now apply sup_unicity with empty.
   apply Hi. now apply from_image. destruct (Hs D). intro. apply H0. apply c with x0.
   now apply sup_unicity with D. apply H2.
 + apply P0_is_smallest_invariant_subCPO. intros x HFx. inversion HFx. now apply S_succ.
   intros D HD. destruct sup_exists with D. exists x. split. now apply S_sup with D. assumption.
Qed.

End S_chain.





Section CounterExample.

 Variant CPO_set : Set := bottom : CPO_set | x1 : CPO_set | x2 : CPO_set.

 Inductive leq3 : rel CPO_set :=
  | reflexive: forall x, leq3 x x
  | bot_x2: leq3 bottom x2
  | bot_x1: leq3 bottom x1
  | x1_x2: leq3 x1 x2.
  
  Instance order_leq3 : PreOrder leq3.
  Proof. repeat constructor. intros x y z.
    intros Hxy Hyz. destruct x; destruct y; destruct z; try constructor;
    try inversion Hxy; try inversion Hyz. Qed.

Program Instance PO_ex : PO CPO_set:=
  {|
    weq x y := leq3 x y /\ leq3 y x;
     leq := leq3;
  |}.
  
  Lemma bot_inf : forall (x : CPO_set), leq bottom x.
  Proof. intro x. case x. reflexivity. apply bot_x1. transitivity x1; constructor. Qed.
  
  Lemma decidable_ex : forall x y, x = y <-> x == y.
  Proof. split; intro H. now rewrite H. inversion H. inversion H0; try reflexivity;
  rewrite <- H2 in *; rewrite <- H3 in *; inversion H1. Qed.

 Program Instance CPO_ex (EM : classic_axiom) : CPO PO_ex :=
  {| 
     sup D x := (D x2 /\ weq x x2) 
                \/ (~ D x2 /\ D x1 /\ weq x x1) 
                \/ (~  D x2 /\ ~ D x1 /\  weq x bottom)
  |}.
  Next Obligation.
    split; intro H. destruct H; destruct H.
    + apply decidable_ex in H0. rewrite H0. 
      intro z. split. intros Hdz y HDy. rewrite <- Hdz. case y; constructor. intro Hz. now apply Hz.
    + destruct H. destruct H0. apply decidable_ex in H1. rewrite H1.
      intro z. split. intros Hdz y HDy. rewrite <- Hdz. destruct y; try constructor. contradiction.
      intro Hz. now apply Hz.
    + destruct H. destruct H0. apply decidable_ex in H1. rewrite H1.
      intro z. split. intros Hdz y HDy. rewrite <- Hdz. destruct y; try constructor. contradiction. contradiction.
      intro Hz. apply bot_inf.
    + destruct (EM (D x2)).
      - destruct (H d) as [Supd _]. left. split; intuition. destruct (H x2) as [_ Infd].
        apply Infd. intros. case y; constructor.
      - right. destruct (EM (D x1)).
        left. destruct (H d) as [Supd _]. split; intuition. destruct (H x1) as [_ Infd].
          apply Infd. intros. destruct y; try constructor. contradiction.
        right. destruct (H d) as [Supd _]. split; intuition. destruct (H bottom) as [_ Infd].
          apply Infd. intros. destruct y; try contradiction. constructor. apply bot_inf.
  Qed.
  Next Obligation. destruct (EM (D x2)). exists x2. now left.
    destruct (EM (D x1)). exists x1. right. now left.
    exists bottom. right. now right. Qed.
  
  Program Instance Lattice_ex (EM : classic_axiom) : CompleteLattice PO_ex :=
  {|
    supL D x := (D x2 /\ weq x x2) 
                \/ (~ D x2 /\ D x1 /\ weq x x1) 
                \/ (~  D x2 /\ ~ D x1 /\  weq x bottom)
  |}.
 Next Obligation.
  split; intro H. destruct H; destruct H.
    + apply decidable_ex in H0. rewrite H0. 
      intro z. split. intros Hdz y HDy. rewrite <- Hdz. case y; constructor. intro Hz. now apply Hz.
    + destruct H. destruct H0. apply decidable_ex in H1. rewrite H1.
      intro z. split. intros Hdz y HDy. rewrite <- Hdz. destruct y; try constructor. contradiction.
      intro Hz. now apply Hz.
    + destruct H. destruct H0. apply decidable_ex in H1. rewrite H1.
      intro z. split. intros Hdz y HDy. rewrite <- Hdz. destruct y; try constructor. contradiction. contradiction.
      intro Hz. apply bot_inf.
    + destruct (EM (Y x2)).
      - destruct (H d) as [Supd _]. left. split; intuition. destruct (H x2) as [_ Infd].
        apply Infd. intros. case y; constructor.
      - right. destruct (EM (Y x1)).
        left. destruct (H d) as [Supd _]. split; intuition. destruct (H x1) as [_ Infd].
          apply Infd. intros. destruct y; try constructor. contradiction.
        right. destruct (H d) as [Supd _]. split; intuition. destruct (H bottom) as [_ Infd].
          apply Infd. intros. destruct y; try contradiction. constructor. apply bot_inf.
  Qed.
  Next Obligation. destruct (EM (D x2)). exists x2. now left.
    destruct (EM (D x1)). exists x1. right. now left.
    exists bottom. right. now right. Qed.
  
  Program Definition F : CPO_set -> CPO_set := fun x => match x with
      | bottom => x2
      | x1 => x1
      | x2 => x2
    end.
 
  Lemma Increasing_F : Increasing F.
  Proof. intro x. destruct x; cbn; constructor. Qed.
  Check is_greatest. Print is_greatest.
 
 Lemma Proper_F : Proper (weq ==> weq) F.
 Proof. intros x y Hxy. apply decidable_ex in Hxy. now rewrite Hxy. Qed.
 
 Lemma all_correct : forall (Y : set CPO_set), Proper (weq ==> iff) Y.
 Proof. intros Y x y Hxy. apply decidable_ex in Hxy. now rewrite Hxy. Qed.
 
 Definition P0_ex (EM : classic_axiom) := (@P0 CPO_set PO_ex (CPO_ex EM) F).
 
 Definition P0' : set CPO_set := fun x => (x == bottom \/ x == x2).
 Lemma P0'_is_invariant_subCPO (EM : classic_axiom) : Invariant F P0' /\ (@is_subCPO CPO_set PO_ex (CPO_ex EM)) P0'.
 Proof. split.
  + intros x Hx. destruct x. now left. inversion Hx. inversion H0; apply decidable_ex in H1; rewrite H1 in H; contradict H;
    now cbn. now right.
  + intros D HDP. destruct (EM (D x2)). exists x2. split. now apply HDP. cbn. now left. exists bottom.
    split. now left. apply sup_spec. intros. split; intuition. destruct y. apply bot_inf. exfalso. apply HDP in H1.
    inversion H1; apply decidable_ex in H2; inversion H2. contradiction. apply bot_inf. Qed.
 
 Lemma P0_is_P0' (EM : classic_axiom) : set_eq (P0_ex EM) P0'.
 Proof. intro. split; intro.
  + apply (H P0'); apply P0'_is_invariant_subCPO; try apply EM; apply decidable_ex in H0; rewrite H0 in *.
  + destruct z. 
    - intros Y Hi Hs. destruct (Hs empty); intuition. intros x Hx. inversion Hx. assert (x == bottom).
      apply weq_spec. split. apply (@bot_spec CPO_set PO_ex (CPO_ex EM)). apply H2. apply bot_inf.
      apply decidable_ex in H0. now rewrite <- H0.
    - inversion H. apply decidable_ex in H0. now rewrite H0 in H. apply decidable_ex in H0. now rewrite H0 in H.
    - intros Y Hi Hs. apply Hi. replace x2 with (F bottom). apply from_image.
        destruct (Hs empty); intuition. intros x Hx. inversion Hx. assert (x == bottom).
        apply weq_spec. split. apply (@bot_spec CPO_set PO_ex (CPO_ex EM)). apply H2. apply bot_inf.
        apply decidable_ex in H0. now rewrite <- H0.
      now cbn.
  Qed.
 
  Lemma top_of_P0_is_not_minimal (EM : classic_axiom) : exists (a : CPO_set), is_greatest (P0_ex EM) a /\ ~ (is_least (Fix F) a).
  Proof.
  destruct (sup_existsL (CompleteLattice := (Lattice_ex EM)) (P0_ex EM)) as [a Ha].
    exists a. split.
    + split.
      - inversion Ha. destruct H. apply decidable_ex in H0. now rewrite <- H0 in H.
        destruct H. destruct H. destruct H0. apply decidable_ex in H1. now rewrite H1.
        destruct H. destruct H0. apply decidable_ex in H1. rewrite H1. apply P0_is_P0'. now left.
      - intros. eapply leq_xsupL. 2 : apply Ha. assumption.
    + intro. destruct H. assert (a <= x1). apply (H0 x1). now cbn.
      assert (x2 <= a). eapply leq_xsupL. 2 : apply Ha. apply P0_is_P0'. now right.
      assert (x2 == a). split. apply H2. destruct a; constructor.
      apply decidable_ex in H3. rewrite <- H3 in H1. inversion H1.
  Qed.



(*  Counter example to the fact that S is a chain is enough to conclude : same CPO *)

Program Definition F' : CPO_set -> CPO_set := fun x => match x with
      | bottom => x2
      | x1 => x2
      | x2 => x1
    end.
 
 Lemma Proper_F' : Proper (weq ==> weq) F'.
 Proof. intros x y Hxy. apply decidable_ex in Hxy. now rewrite Hxy. Qed.

 Definition P0_ex' (EM : classic_axiom) := (@P0 CPO_set PO_ex (CPO_ex EM) F').

Lemma S_chain (EM : classic_axiom) : is_Chain (S (P := (CPO_ex EM)) F').
Proof.
  intros x y HSx HSy. destruct x. left. apply bot_inf. destruct y. right. apply bot_inf.
  left. apply reflexivity. left. constructor. destruct y. right. apply bot_inf.
  right. constructor. left. reflexivity.
Qed.

Lemma no_fixpoint' : ~ (exists x, Fix F' x).
Proof.
  intro H. destruct H. destruct x; apply decidable_ex in H; cbn in H; inversion H.
Qed.

End CounterExample.


