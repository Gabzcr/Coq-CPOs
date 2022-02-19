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

(* Definition of a CPO : Complete Partially Ordered set, and Lattice as a particular (stronger) CPO. *)
Class CPO (X: Type) := {
  weq: relation X;
  leq: relation X;
  sup: directed_set leq -> X;
  PreOrder_leq:> PreOrder leq;
  weq_spec: forall x y, weq x y <-> (leq x y /\ leq y x);
  sup_spec: forall D z, (leq (sup D) z <-> forall (y:X), (Dbody D) y -> leq y z);
}.

Class CompleteLattice (X : Type) `(L : CPO X) := {
    sup_lat: (X -> Prop) -> X;
    sup_spec_lat:  forall Y z, (leq (sup_lat Y) z <-> forall y, Y y -> leq y z);
}.

Declare Scope CPO. (* I don't really understand there 2 lines. *)
Open Scope CPO.
Infix "==" := weq (at level 70): CPO.
Infix "<=" := leq: CPO.
Global Hint Extern 0 => reflexivity: core.

(** * Utilities  *)

(** any monotone function preserves equality  *)
Lemma op_leq_weq_1 {X Y} {LX: CPO X} {LY: CPO Y} {f: X -> Y}
  {Hf: Proper (leq ==> leq) f}: Proper (weq ==> weq) f.
Proof. intros x y. rewrite 2weq_spec. intro E; split; apply Hf; apply E. Qed.

Lemma op_leq_weq_2 {X Y Z} {LX: CPO X} {LY: CPO Y} {LZ: CPO Z} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq ==> leq) f}: Proper (weq ==> weq ==> weq) f.
Proof.
  intros x y E x' y' E'. rewrite weq_spec in E. rewrite weq_spec in E'.
  apply weq_spec. split; apply Hf; (apply E || apply E').
Qed.


(** * Sets general properties *)

Section Sets.

 Context {X} {P: CPO X}.

 Definition iff_part (f g : X -> Prop) := forall z, f z <-> g z. (*equality of sets*)

 Definition included (S T: set X) := forall x, S x -> T x.

 #[global] Instance Included_trans : Transitive included.
 Proof.
  intros Y1 Y2 Y3 H12 H13. intros x H. apply H13. now apply H12.
 Qed.

End Sets.
Infix "⊆" := included (at level 70).


(** * Directedness general properties *)

Section Directedness.

 Context {X} {P: CPO X}.

 Lemma directed_symmetry f g : (forall z, f z <-> g z) -> Directed leq f <-> Directed leq g.
 Proof. intro H. unfold Directed. setoid_rewrite H. tauto. Qed.

 #[global] Instance directed_eq : Proper (iff_part ==> iff) (Directed leq).
 Proof. intros f g. apply directed_symmetry. Qed.

 Lemma singleton_is_directed x : Directed leq (fun z => z=x).
 Proof. unfold Directed. intros y z Hyz. exists x. repeat split. now rewrite Hyz. now rewrite H. Qed.

Definition is_Chain (Y : set X) := forall (x y : X), Y x -> Y y -> x <= y \/ y <= x.

Lemma chain_is_directed {Y} {Q : CPO Y} : forall D, is_Chain D -> Directed leq D.
Proof.
  intros D Hd x y Hx Hy. destruct (Hd x y); intuition.
  exists y. now split.
  exists x. now split.
Qed.


End Directedness.

(** Partial Order general properties *)

Section Partial_order.

 Context {X} {P: CPO X}.

 #[global] Instance Equivalence_weq: Equivalence weq.
 Proof.
   constructor.
    intro x. now apply weq_spec.
    intros x y. rewrite 2weq_spec. tauto.
    intros x y z. rewrite 3weq_spec. split; transitivity y; tauto.
 Qed.

 Global Instance PartialOrder_weq_leq: PartialOrder weq leq.
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

 Context {X} {P: CPO X} `{L : CompleteLattice X}.

 Lemma leq_xsup D y: (Dbody D) y -> y <= sup D.
 Proof. intro H. now apply (sup_spec D). Qed.

 Lemma leq_xsup_lat (Y:X->Prop) y : Y y -> y <= sup_lat Y.
 Proof. intro H. now apply (sup_spec_lat Y). Qed.

 Lemma sup_is_independent_of_proof : forall D_dir D_dir2, iff_part (Dbody D_dir) (Dbody D_dir2)
   -> sup D_dir == sup D_dir2.
 Proof.
  intros. apply weq_spec. split; apply sup_spec; intros; apply leq_xsup;
  now apply H.
 Qed.

 Program Definition empty {Y} {Q : CPO Y}: (directed_set leq) := exist _ (fun _ => False) _.
 Next Obligation. unfold Directed. intros. contradict H. Defined.

 Definition bot := sup empty. (*Warning : with our current definition of directed,
 bottom exists since the empty set is directed. Later, we might want to change that to allow bottom to no exist*)

 Lemma bot_spec: forall x, bot <= x.
 Proof. intro. now apply sup_spec. Qed.

 Definition top_lat := sup_lat (fun _ => True). (* Rmk : only exists in lattices, not just CPOs. *)

 Lemma top_spec_lat: forall x, x <= top_lat.
 Proof. intro. now apply leq_xsup_lat. Qed.

 (** Inf *)

 Definition inf_lat Y := sup_lat (fun z => forall y, Y y -> z <= y).
 Lemma inf_spec_lat: forall Y z, z <= inf_lat Y <-> (forall y, Y y -> z <= y).
 Proof.
   intros. unfold sup. split.
   intros H y Yy. rewrite H; apply sup_spec_lat. now auto.
   intro. now apply leq_xsup_lat.
 Qed.

  Lemma leq_xinf (D: X -> Prop) y:  D y -> inf_lat D <= y.
 Proof. intro H. now apply inf_spec_lat with D. Qed.


(* --- Inclusion of sets and sup --- *)

 Definition included_body (S T : directed_set leq) := (Dbody S) ⊆ (Dbody T).
 #[global] Instance sup_preserves_inclusion: Proper (included_body ==> leq) sup.
 Proof.
  intros S T HST. apply sup_spec. intros. apply leq_xsup.
  now apply HST.
 Qed.

 Definition iff_part_body (S T : directed_set leq) := iff_part (Dbody S) (Dbody T).
 #[global] Instance sup_preserves_equality: Proper (iff_part_body ==> weq) sup.
 Proof.
  intros S T HST. apply weq_spec. split; apply sup_preserves_inclusion; intros x Hx; now apply HST.
 Qed.

End sup.

Global Hint Resolve bot_spec: core.



(** * Monotonous functions and other properties *)

Section functions.
 Context {X} {P: CPO X}.

 Definition Fix F x := F x == x.
 Definition Post F x := x <= F x.
 Definition Pre F x := F x <= x.

 Lemma fix_is_post F : forall x, Fix F x -> Post F x.
 Proof. intros. apply weq_spec in H. apply H. Qed.
 Lemma fix_is_pre F : forall x, Fix F x -> Pre F x.
 Proof. intros. apply weq_spec in H. apply H. Qed.


 (* Monotonous functions *)

 Record mon := { body:> X -> X; Hbody: Proper (leq ==> leq) body }.

 #[global] Instance Hbody' (F:mon) : Proper (weq ==> weq) F.
 Proof. apply (op_leq_weq_1 (Hf:=(Hbody F))). Qed.

 Inductive Image f (S : X -> Prop) : X -> Prop :=
  |from_image : forall x, S x -> Image f S (f x).

 Definition Continuous f := forall (D : set X) (H : Directed leq D), {dir_im : Directed leq (Image f D) &
  f (sup (exist _ D H )) == sup (exist _ (Image f D) dir_im)}.

 Lemma mon_preserves_directedness_and_sup (F:mon) : forall (D : set X) (H : Directed leq D), {dir_im : Directed leq (Image F D) &
  sup (exist _ (Image F D) dir_im) <= F (sup (exist _ D H ))}.
 Proof.
  intros. assert (Directed leq (Image F D)).
  + unfold Directed. intros. inversion H0. inversion H1.
    destruct (H x0 x1); try assumption. exists (F x2).
    repeat split; try apply Hbody; apply H6.
  + exists H0. apply sup_spec; cbn. intros.
    inversion H1. apply Hbody. now apply leq_xsup.
 Qed.


 (* Some basic monotonous functions *)

 Program Definition const x: mon := {| body y := x |}.
 Next Obligation. intros ? ? ?. reflexivity. Qed.

 Definition id: mon := {|
   body x := x;
   Hbody x y H := H
 |}.

 Definition comp {Y} {Q : CPO Y} (f g: mon): mon := {|
   body := fun x => f (g x);
   Hbody x y H := Hbody f _ _ (Hbody g _ _ H)
 |}.
 Infix "°" := comp (at level 20): CPO.


 (* Iterations of a function *)

 Fixpoint itere F n x0 : X := match n with
  | 0 => x0
  | S m => F (itere F m x0)
 end. (*Indexed by n for simplicity on comparison properties.*)

 Lemma itere_monotony (F:mon) : forall n, Proper (leq ==> leq) (itere F n).
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

 Inductive iteres F : X -> Prop :=
  | from_bot : forall n, iteres F (itere F n bot).

 Lemma iteres_directed (F:mon): Directed leq (iteres F).
 Proof.
  unfold Directed. intros. destruct H. destruct H0.
  destruct le_ge_dec with n n0.
  + exists (itere F n0 bot). repeat split. now apply chain_increase. reflexivity.
  + exists (itere F n bot). repeat split. reflexivity. now apply chain_increase.
 Qed.

 Inductive iteres_from_1 F : X -> Prop :=
  | from_bot_from_1 : forall n,  le 1 n -> iteres_from_1 F (itere F n bot).

 Lemma iteres_from_1_directed (F:mon): Directed leq (iteres_from_1 F).
 Proof.
  unfold Directed. intros. destruct H. destruct H0.
  destruct le_ge_dec with n n0.
  + exists (itere F n0 bot). repeat split. assumption. now apply chain_increase. reflexivity.
  + exists (itere F n bot). repeat split. assumption. reflexivity. now apply chain_increase.
 Qed.

 Lemma image_of_iteres F : iff_part (Image F (iteres F)) (iteres_from_1 F).
 Proof.
  intro. split; intro; inversion H. inversion H0.
  + assert (iteres_from_1 F (itere F (S n) bot)). apply from_bot_from_1. lia.
    apply H3.
  + induction n. contradict H0. lia.
    cbn. apply from_image. apply from_bot.
 Qed.

 Lemma from_1_included F : included (iteres_from_1 F) (iteres F).
 Proof. intros x H. inversion H. apply from_bot. Qed.

End functions.


Section Particular_CPOs.

 Context {X} {P: CPO X}.

 Program Instance CPO_mon : CPO mon := {|
   weq := pointwise_relation X weq;
   leq := pointwise_relation X leq;
   sup F := {| body a := sup (fun b => exists2 f, F f & b=f a) |};
 |}.
 Next Obligation.
  unfold Directed. intros. destruct F as [SF D]; cbn in *.
  destruct H as [fx Hfx]. destruct H0 as [fy Hfy].
  destruct (D fx fy) as [f [Hf1S [Hff1 Hff2]]]; try assumption.
  exists (f a). repeat split. now exists f.
  + rewrite H. apply Hff1.
  + rewrite H0. apply Hff2.
 Qed.
 Next Obligation.
  destruct F as [SF D]; cbn in *.
  intros x y H. apply sup_spec; cbn. intros.
  destruct H0 as [f Hf].
  transitivity (f y). rewrite H0. now apply Hbody.
  apply leq_xsup. cbn. now exists f.
 Qed.
 Next Obligation. (*Rmk : symbol ":>" is to declare a trivial instance.*)
  apply Build_PreOrder.
  + intro x. reflexivity.
  + intros f g h Hfg Hgh x. now transitivity (g x).
 Qed.
 Next Obligation.
  split; intros.
  + split; intro a; now apply weq_spec.
  + intro. now apply weq_spec.
 Qed.
 Next Obligation.
  destruct D as [SF D]; cbn in *. split.
  + intros H f Df x. rewrite <- (H x).
  eapply sup_spec. reflexivity. cbn. now exists f.
  + intros H x. apply sup_spec. intros. inversion H0. rewrite H2. now apply (H x0).
 Qed.

 Program Instance CPO_parts: CPO (set X) := {|
   weq := iff_part;
   leq := included;
   sup A := (fun x => exists Y, A Y /\ Y x);
 |}.
 Next Obligation.
  apply Build_PreOrder.
  + intro Y. now intro x.
  + apply Included_trans.
 Qed.
 Next Obligation.
  repeat split; try intuition; intros a; intro H0; apply H; try apply H0.
 Qed.
 Next Obligation.
  split; intros; intros a Ha. apply H. now exists y.
  destruct Ha. apply (H x). apply H0. apply H0.
 Qed.

 Program Instance Lattice_parts : CompleteLattice (CPO_parts) := {|
  sup_lat A := (fun x => exists Y, A Y /\ Y x);
 |}.
 Next Obligation.
  split; intros; intros a Ha. apply H. now exists y.
  destruct Ha. apply (H x). apply H0. apply H0.
 Qed.


 (** * sub-CPO : Define a set (part of X) as being a CPO *)

 Definition is_subCPO (Y : set X) := forall D, included (Dbody D) Y -> Y (sup D).

 Definition down (x:X) := (fun z => z <= x).

 Lemma down_is_subCPO : forall x, is_subCPO (down x).
 Proof. intros x D Hd. unfold down. apply sup_spec. intros. now apply Hd. Qed.

 Definition set_type (Y : set X) : Type := { x : X | Y x}.
 Definition element Y (y :set_type Y) := proj1_sig y.

 Definition complete_body {Y : set X} (D : set (set_type Y)) : set X :=
  (fun x => {is_in_Y : Y x & D (exist _ x is_in_Y)}).

 Program Definition subCPO (*{X} {P : CPO X}*) (Y:set X) (H : is_subCPO Y) : (CPO (set_type Y)) := {|
   weq x y := (@weq X P) (element x) (element y);
   leq x y := (@leq X P) (element x) (element y);
   sup D := (@sup X P) (exist (Directed leq) (complete_body (Dbody D)) _) ;
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
 Next Obligation. apply Build_PreOrder; intro x. reflexivity. intros y z Hxy Hyz. now transitivity (element y). Qed.
 Next Obligation. apply weq_spec. Qed.
 Next Obligation. split.
  + intros. apply (sup_spec (exist (Directed leq) (complete_body (Dbody D)) (subCPO_obligation_1 D))); cbn.
    assumption. destruct y. cbn. now exists y.
  + intros. apply sup_spec. cbn. intros. destruct H1. now apply (H0 (exist (fun x : X => Y x) y x)).
 Qed.


(* Some instances that can now be defined on CPO_parts and CPO_mon. *)

 Variable F : X -> X.

 #[global] Instance image_eq : Proper (weq ==> weq) (Image F).
 Proof. intros Y1 Y2 HY. split; intro H; inversion H; apply from_image; now apply HY. Qed.

 #[global] Instance set_incl : Proper (weq ==> weq ==> iff) included.
 Proof. intros Y1 Y2 H12 Y3 Y4 H34. split; intros Hi x Hx; apply H34; apply Hi; now apply H12. Qed.

 Lemma set_eq : forall (f g : set X), f == g -> (pointwise_relation X iff) f g.
 Proof.
  intros f g H x. split; intro Hh; apply weq_spec in H; destruct H.
  now apply H. now apply H0.
 Qed.

End Particular_CPOs.


Ltac rew H H' :=
  let eq := fresh in
  pose proof @set_eq _ _ H as eq;
  apply eq in H';
  clear eq.

Ltac rew_goal H :=
  let eq := fresh in
  pose proof @set_eq _ _ H as eq;
  apply eq;
  clear eq.

Tactic Notation "prew" hyp(H) "in" hyp(H') := rew H H'.
Tactic Notation "prew" constr(H) "in" hyp(H') := rew H H'.
Tactic Notation "prew" hyp(H)    := rew_goal H.
Tactic Notation "prew" constr(H) := rew_goal H.



(** * Common fixpoint of every monotonous increasing function *)

Section Increasing_fixpoint.
 Context {X} {P: CPO X}.

 Definition Increasing F := forall x, x <= F x.

 Definition leq_mon := (@leq mon CPO_mon).
 Definition weq_mon := (@weq mon CPO_mon).

 Program Definition Increasing_functions := exist (Directed leq_mon) Increasing _.
 Next Obligation.
  unfold Directed. intros f g Hf Hg. exists (comp f g). repeat split.
  + intro x. transitivity (g x). apply Hg. apply Hf.
  + intro x. cbn. apply Hbody. apply Hg.
  + intro x. cbn. apply Hf.
 Defined.

 Definition H_sup := (sup Increasing_functions).

 Lemma H_sup_is_increasing : Increasing H_sup.
 Proof. intro. assert (leq_mon id H_sup). now apply (sup_spec Increasing_functions). apply H. Qed.

 Lemma H_sup_bot_is_fixpoint_of_all_Increasing (F:mon) :
  Increasing F -> Fix F (H_sup bot).
 Proof.
  intro. assert (weq_mon (comp F H_sup) H_sup).
  + apply weq_spec. split. apply (sup_spec Increasing_functions). reflexivity.
    intro x. transitivity (H_sup x). apply H_sup_is_increasing. apply H.
    intro. apply H.
  + unfold Fix. now setoid_rewrite (H0 bot).
 Qed.

 (* Lemma 8.21*)
 Lemma increasing_has_fix_point (F:mon) : Increasing F -> exists x, Fix F x.
 Proof.
  intro. exists (H_sup bot). now apply H_sup_bot_is_fixpoint_of_all_Increasing.
 Qed.

 End Increasing_fixpoint.



(** * Invariant subCPOs *)

Section Invariant_subCPOs.

 Context {X} {P: CPO X}.

 Definition Invariant (F : X -> X) Y := included (Image F Y) Y.

Variable F : X -> X.

 Definition P0 :=  (*P0 is the smallest invariant subCPO : intersection of all invariant sub_CPOs.*)
  (fun x => forall Y, Invariant F Y -> is_subCPO Y -> Y x).

 Lemma P0_is_invariant_subCPO : Invariant F P0 /\ is_subCPO P0.
 Proof.
  split.
  + intros x H. inversion H. intros Y Hi Hs. apply Hi. apply from_image. now apply (H0 Y).
  + intros D H Y Hi Hs. apply Hs. rewrite H. intros x Hx. now apply Hx.
 Qed.

 Lemma P0_is_smallest_invariant_subCPO : forall Y, Invariant F Y -> is_subCPO Y -> included P0 Y.
 Proof. intros Y Hi Hs x Hx. now apply Hx. Qed.

End Invariant_subCPOs.



(* Knaster-Tarski Theorem on Lattices *)

Section lattice_results.
 Context {X} `{L: CompleteLattice X}.
 Variable b: mon.

 Definition gfp := sup_lat (fun x => x <= b x).
 Definition lfp := inf_lat (fun x => b x <= x).

 Proposition leq_gfp: forall y, y <= b y -> y <= gfp.
 Proof. apply leq_xsup_lat. Qed.
 Proposition geq_lfp: forall y, b y <= y -> lfp <= y.
 Proof. apply leq_xinf. Qed.

 Lemma gfp_pfp: gfp <= b gfp.
 Proof.
  unfold gfp. apply sup_spec_lat. intros y H. rewrite H. apply Hbody.
  apply leq_xsup_lat. apply H.
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
    + apply leq_xsup_lat. apply Hbody. apply gfp_pfp.
 Qed.
 Lemma lfp_fp: lfp == b lfp.
 Proof.
  rewrite weq_spec. split.
    + apply leq_xinf. apply Hbody. apply lfp_pfp.
    + apply lfp_pfp.
 Qed.

End lattice_results.



Section Using_Tarski.
(* Remark : although this section is used in the proofs of the book, it is not used throughout this file.
It is enough to work with P0 as the smallest invariant subCPO, no need to use its properties of least fixpoint. *)

 Context {X} {P: CPO X}.

 Program Definition Φ F' : @mon (set X) (CPO_parts) :=  (*since def of mon is linked to that of CPOs, need a CPO of parts*)
  {| body X := (fun x => (x = bot \/ (Image F' X) x \/ (exists D, included (Dbody D) X /\ x = sup D))) |}.
 Next Obligation.
  intros Y1 Y2 H12 x Hx. destruct Hx; intuition.
  + right. left. inversion H0. apply from_image. now apply H12.
  + destruct H0 as [Hd [Hi Hs]]. right. right. exists Hd. split.
    intros y Hy. apply H12. now apply Hi. assumption.
 Qed.

 Definition P0' F' := (@lfp (set X) CPO_parts Lattice_parts) (Φ F').

 Lemma P0_is_P0' F : (@weq (set X) CPO_parts) (P0 F) (P0' F).
 Proof.
  apply weq_spec. split.
  + apply P0_is_smallest_invariant_subCPO.
    - unfold Invariant. unfold P0'. rewrite lfp_fp at 2.
      intros x H. right. now left.
    - unfold is_subCPO. unfold P0'. intros D H.
      apply (set_eq (lfp_fp (Φ F))). (* prew does not work *)
      right. right. now exists D.
  + unfold P0'. apply geq_lfp. intros x H.
    destruct (P0_is_invariant_subCPO F). destruct H. rewrite H.
    apply (H1 empty). intros y Hy. contradict Hy.
    destruct H. inversion H. apply H0. now apply from_image.
    destruct H as [D [Hd Hs]]. rewrite Hs. now apply (H1 D).
 Qed.

End Using_Tarski.



(** * Fixpoint theorems ! *)

Section Fixpoints.
 Context {X} {P: CPO X}.

 Definition is_least {Y} {Q : CPO Y} S x := S x /\ forall y, S y -> x <= y.
 Definition is_inf {Y} {Q : CPO Y} S x := forall z, (forall y, S y -> z <= y) <-> z <= x.
 Definition is_minimal {Y} {Q : CPO Y} S x := S x /\ forall y, S y -> y <= x -> y == x.
 Definition is_greatest {Y} {Q : CPO Y} S x := S x /\ forall y, S y -> y <= x.
 Definition is_sup {Y} {Q : CPO Y} S x := forall z, (forall y, S y -> y <= z) <-> x <= z.

 Lemma test_coherence1 : forall D, is_sup (Dbody D) (sup D).
 Proof. intros D z. split; apply sup_spec. Qed.
 Lemma test_coherence2 : forall D, (Dbody D) (sup D) -> is_greatest (Dbody D) (sup D).
 Proof. intros. split. assumption. now apply sup_spec. Qed.


 (** * Fixpoint theorems and proofs : first theorem. *)
 Variable F:mon.

 Program Definition α := (sup (exist _ (iteres F) (iteres_directed F))).

 Theorem Fixpoint_I_i : Fix F α -> is_least (Fix F) α.
 Proof.
 intro H. split; try assumption.
  intros. apply sup_spec; cbn. intros z Q.
  inversion Q. rewrite <- (itere_preserves_fix F y n).
  now apply itere_monotony. assumption.
 Qed.

 Program Definition α' := (sup (exist _ (iteres_from_1 F) _)).
 Next Obligation. apply iteres_from_1_directed. Qed.

 Lemma sup_from_1 : α == α'.
 Proof.
  apply weq_spec. split.
  + apply sup_spec; cbn. intros. inversion H.
  induction n. now cbn. apply leq_xsup.
  apply from_bot_from_1. lia.
  + apply sup_preserves_inclusion; cbn. apply from_1_included.
 Qed.

 Theorem Fixpoint_I_ii : Continuous F -> is_least (Fix F) α. (* Note that F is monotonous too. *)
 Proof.
  intro H.
  assert (Fix F α).
   + unfold Fix. destruct (H (iteres F) (iteres_directed F)) as [HD HS].
    transitivity α'; try now rewrite sup_from_1. rewrite HS.
    apply sup_is_independent_of_proof. cbn. unfold iff_part. apply image_of_iteres.
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

Lemma P0_is_in_Post : included (P0 F) (Post F).
Proof.
  assert (Invariant F (Post F) /\ is_subCPO (Post F)).
  + split.
    - intros x H. inversion H. apply Hbody. apply H0.
    - intros D H. apply sup_spec. intros. transitivity (F y). now apply H.
      apply Hbody. now apply leq_xsup.
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

 Program Instance P0_CPO : CPO (set_type (P0 F)) := (subCPO _).
 Next Obligation. apply P0_is_invariant_subCPO. Qed.

 Program Definition F_restricted_to_P0 : @mon (set_type (P0 F)) P0_CPO :=
  {| body := fun y => (exist _ (F (element y)) _) |}.
 Next Obligation. destruct y as [x Hx]; cbn. apply P0_is_invariant_subCPO. now apply from_image. Qed.
 Next Obligation. intros y1 y2 H12; cbn. now apply Hbody. Qed.

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

 Theorem a_is_top_of_P0_and_least_fixpoint_of_F : is_greatest (P0 F) (element a) /\ is_least (Fix F) (element a).
 Proof. split.
  + split. destruct a as [µ Hmu]. now cbn. apply P0_is_in_down.
   intros. apply a_is_fixpoint_of_F.
  + split. apply a_is_fixpoint_of_F. intros. apply (P0_is_in_down y).
    assumption. destruct a as [µ Hmu]. now cbn.
 Qed.

End Fixpoints.




(** * Theorem III : Bourbaki-Witt theorem. This theorem requires classic logic, it is false in intuitionist logic. *)

Section Bourbaki_Witt.

 Context {X} {P: CPO X}.
 Definition classic_axiom := forall (P : Prop), P \/ ~ P.

 (* Now show that P0 is a chain, to prove that it has a sup (top). This is a fixpoint. *)

 Definition lt {Y} {Q : CPO Y} x y := x <= y /\ ~ (x == y).
 Infix "<" := lt.

 Lemma leq_is_lt_or_eq : classic_axiom -> forall x y, x <= y -> x==y \/ x < y. (* excluded middle ! *)
 Proof. intros EM x y Hxy. destruct (EM (x==y)). now left. now right. Qed.

 Lemma not_leq_and_gt : forall x y, ~ (x <= y /\ y < x). (* no need for EM *)
 Proof. intros x y. intro. destruct H. destruct H0. contradict H1. now apply weq_spec. Qed.

 Definition Extreme F' : set X :=
  (fun c => (P0 F') c /\ forall x, (P0 F') x -> x < c -> F' x <= c).

 Definition Mc F' c : set X :=
  (fun x => (P0 F') x /\ (x <= c \/ F' c <= x)).

 Lemma Mc_is_P0 F' : classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> forall c, Extreme F' c -> iff_part (P0 F') (Mc F' c).
 Proof.
  intros EM Fp HF c Ec. destruct Ec as [Pc Ec']. split.
  + apply P0_is_smallest_invariant_subCPO.
    - intros x Hx. inversion Hx. split. apply P0_is_invariant_subCPO. apply from_image. apply H.
      destruct H as [Px0 Hx0]. destruct Hx0.
      * apply leq_is_lt_or_eq in H. destruct H. right. apply weq_spec. now apply Fp.
        left. now apply Ec'. assumption.
      * right. transitivity x0. assumption. apply HF.
    - intros D Hi. split.
      apply P0_is_invariant_subCPO. rewrite Hi. intros x0 Hx0. apply Hx0.
      destruct (EM (exists y, (Dbody D) y /\ F' c <= y)). (* WARNING : excluded middle ! *)
      * right. destruct H as [y Hy]. transitivity y. apply Hy. now apply leq_xsup.
      * left. apply sup_spec. intros. destruct (Hi y). assumption.
        destruct H2. assumption. contradict H. now exists y.
  + intro Hm. apply Hm.
 Qed.

 Lemma P0_is_extreme F' : classic_axiom -> (Proper (weq ==> weq) F') ->  Increasing F' -> forall x, P0 F' x -> Extreme F' x.
 Proof.
  intros EM Fp HF. apply P0_is_smallest_invariant_subCPO.
  + intros c Hc. inversion Hc. inversion H as [HPx HEx]. split.
    - apply P0_is_invariant_subCPO. now apply from_image.
    - intros. assert (iff_part (P0 F') (Mc F' x)). apply (Mc_is_P0 EM Fp HF H).
      assert (Mc F' x x0). now rewrite <- (set_eq H3 x0). destruct H4. destruct H5.
      * apply leq_is_lt_or_eq in H5; intuition.
        apply weq_spec. now apply Fp. transitivity x; intuition.
      * exfalso. eapply not_leq_and_gt. split. apply H5. apply H2.
  + intros D Ed. split. apply P0_is_invariant_subCPO. rewrite Ed. intros x Hx. apply Hx.
    intros x Px Hxd. destruct (EM (exists c, (Dbody D) c /\ x <= c)).
    - destruct H as [c [Hdc Hcx]]. apply leq_is_lt_or_eq in Hcx; intuition.
      * transitivity (F' c). apply weq_spec. now apply Fp.
        assert (Mc F' c (sup D)). apply Mc_is_P0; intuition. apply P0_is_invariant_subCPO.
          rewrite Ed. intros y Hy. apply Hy.
        destruct H0. destruct H1. exfalso. eapply not_leq_and_gt. split. rewrite <- H in H1.
        apply H1. apply Hxd. assumption.
      * transitivity c. apply Ed; intuition. now apply leq_xsup.
    - assert (sup D <= x).
      * apply sup_spec. intros. rewrite HF. assert (Mc F' y x). apply Mc_is_P0; intuition.
        destruct H1. destruct H2. contradict H. now exists y. assumption.
      * exfalso. eapply not_leq_and_gt. split. apply H0. assumption.
 Qed.


 Lemma P0_is_Chain (F':X -> X) : classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> is_Chain (P0 F').
 Proof.
  intros EM Fp HF x y Hx Hy. assert (Mc F' x y).
  apply Mc_is_P0; intuition. apply P0_is_extreme; intuition.
  destruct H. destruct H0. now right. left. transitivity (F' x).
  apply HF. assumption.
 Qed.

 Lemma P0_is_directed (F':X -> X) : classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> Directed leq (P0 F').
 Proof. intros EM Fp HF. apply chain_is_directed. now apply P0_is_Chain. Qed.

(* Note : since we put excluded middle and functional extensionality as hypothesis, we lose constructivity,
we can't just define our fixpoint as below :
Program Definition top_P0 (F':X -> X) (H : Increasing F') := (sup (exist _ (P0 F') _)).
Next Obligation. apply P0_is_directed; intuition. apply H. Qed. *)

(*The book is wrong : the top of P0 is not necessarily minimal (cf counterexample on paper)
However, from an existing fix point, it seems we can deduce a minimal fix point since the set of
fixpoints between bottom and our fix point is a chain. TODO ? *)
 Theorem Fixpoint_III (F' : X -> X) : classic_axiom -> (Proper (weq ==> weq) F') -> Increasing F' -> exists x, Fix F' x(*is_minimal (Fix F') x*).
 Proof.
  intros EM Fp HF. exists (sup (exist _ (P0 F') (P0_is_directed EM Fp HF))).
  apply weq_spec. split. apply leq_xsup; cbn. apply P0_is_invariant_subCPO.
  apply from_image. apply P0_is_invariant_subCPO; cbn. intro. now intro.
  apply sup_spec; cbn. intros. rewrite <- HF. now apply leq_xsup.
 Qed.

End Bourbaki_Witt.
