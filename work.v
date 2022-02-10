

(** * Adapting to CPOs *)

From Coq Require Import Arith.
Require Import Psatz.
Require Export Setoid Morphisms.
Set Implicit Arguments.

(*
Definition even_type : Type := {n:nat | Arith.Even.even n}.
Lemma is_not_odd (n:even_type) : ~ Arith.Even.odd (proj1_sig n).
Proof.
  destruct n. cbn. intuition.
Admitted.
*)

(*
Definition Directed_generalized X (D:X->Prop) (leq : relation X) := 
  forall x y, D x -> D y -> exists z, D z /\ leq x z /\ leq y z.
Definition directed_set_generalized X (Directed : (X -> Prop) -> Prop) : Type :=
  {Dbody : X -> Prop | Directed Dbody}.
Definition Dbody_generalized X P (D:sig P) : X -> Prop :=
  proj1_sig D.
*)

Class CPO (X: Type) := {
  weq: relation X;
  leq: relation X;
  Directed (D: X -> Prop) := forall x y, D x -> D y -> exists z, D z /\ leq x z /\ leq y z;
  directed_set : Type := {Dbody : X -> Prop | Directed Dbody};
  Dbody (D:directed_set) : X -> Prop :=  proj1_sig D;
  sup: directed_set -> X;
  PreOrder_leq:> PreOrder leq;
  weq_spec: forall x y, weq x y <-> (leq x y /\ leq y x);
  sup_spec: forall D z, (leq (sup D) z <-> forall (y:X), (Dbody D) y -> leq y z);
                        }.

(*
Class CPO (X: Type) := {
  weq: relation X;
  leq: relation X;
  sup: (X -> Prop) -> X -> Prop;
  PreOrder_leq:> PreOrder leq;
  Directed (D: X -> Prop) := forall x y, D x -> D y -> exists z, D z /\ leq x z /\ leq y z;
  weq_spec: forall x y, weq x y <-> (leq x y /\ leq y x);
  sup_spec: forall D s, sup D s -> forall z, (leq s z <-> forall y, D y -> leq y z);
  sup_exists: forall D, Directed D -> exists s, sup D s;
  (*sup_spec: forall Y z, Directed Y ->  (leq (sup Y) z <-> forall y, Y y -> leq y z);*)
                        }.*)

Class CompleteLattice (X : Type) `(L : CPO X) := {
    sup_lat: (X -> Prop) -> X;
    sup_spec_lat:  forall Y z, (leq (sup_lat Y) z <-> forall y, Y y -> leq y z);
                                  }.
Declare Scope CPO.
Open Scope CPO.
Infix "==" := weq (at level 70): CPO.
Infix "<=" := leq: CPO.
Global Hint Extern 0 => reflexivity: core.

(** * Reversing a CPO *)

Definition reverse_leq X (leq : X -> X -> Prop) : X -> X -> Prop := fun x y => leq y x.

Global Program Instance reverse_CPO (P: CPO X): CPO X := {|
   weq := weq;
   leq := reverse_leq leq;
   sup D := sup (fun z => forall y, (@Dbody X (reverse_CPO X) D y) -> leq z y); 
   (*Careful ! I dunno which "leq" is used here :/*)
 |}.


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

(** * General properties of complete lattices *)

Section sup.
 Context {X} {P Q: CPO X} `{L : CompleteLattice X}.
 
 (*Below lemma is necessary for later property.*)
 Lemma directed_symmetry f g : (forall z, f z <-> g z) -> Directed f <-> Directed g.
 Proof.
  intro H. unfold Directed. (* unfold Directed_generalized. *)setoid_rewrite H. tauto.
Qed.

Definition iff_part (f g : X -> Prop) := forall z, f z <-> g z.
Locate "<->".
Global Instance directed_eq : Proper (iff_part ==> iff) Directed.
Proof. intros f g. apply directed_symmetry. Qed.

Lemma singleton_is_directed x : Directed (fun z => z=x).
Proof.
  unfold Directed. intros. exists x. repeat split. now rewrite H. now rewrite H0.
Qed.


 (** Partial order *)
 Global Instance Equivalence_weq: Equivalence weq.
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

(*
 Global Instance sup_leq:
   Proper (leq ==> leq) sup.
 Proof.
   intros P P' HP. apply sup_spec.
   setoid_rewrite HP. 
   now apply sup_spec.
 Qed.
 Global Instance sup_weq: Proper (weq ==> weq) sup := op_leq_weq_1.*)
 
 Lemma leq_xsup D y: (Dbody D) y -> y <= sup D.
 Proof. intro H. now apply (sup_spec D). Qed.
 
 Lemma leq_xsup_lat (Y:X->Prop) y : Y y -> y <= sup_lat Y.
 Proof. intro H. now apply (sup_spec_lat Y). Qed.

(*
Lemma sup_unicity D s1 s2: sup D s1 -> sup D s2 -> s1 == s2.
Proof.
  intros. apply weq_spec. split; [apply (sup_spec D s1) | apply (sup_spec D s2)]; try assumption.
  now apply (sup_spec D s2). now apply (sup_spec D s1).
Qed.*)

Program Definition empty : directed_set := exist _ (fun _ => False) _.
Next Obligation.
unfold Directed. (* unfold Directed_generalized.*) intros. contradict H.
Defined.

(* Above is better and equivalent, I keep this here to remember what I learned on Sig today *)
(*
Lemma empty_is_directed : (Directed (fun _ => False)).
Proof. unfold Directed. intros. contradict H. Qed.
Definition empty : directed_set := exist Directed (fun _ => False) empty_is_directed.
*)

 Definition bot := sup empty. (*Warning : with our current definition of directed,
 bottom exists since empty set is directed. Later, we will want to change that to allow bottom to no exist*)
 Lemma bot_spec: forall x, bot <= x.
 Proof. intro. now apply sup_spec. Qed.

 Definition top := sup_lat (fun _ => True).
 Lemma top_spec_lat: forall x, x <= top.
 Proof. intro. now apply leq_xsup_lat. Qed.
(*Not in CPOs ! We don't want CPOs to have a top, otherwise just word with Complete Lattices already.*)

(* Following section : not really handy for CPOs, since cup and cap only exists if {x,y} is directed, 
i.e. x and y are comparable. Forget it for now, may be of use later with lattices *)
(*
 Definition cup x y := sup (fun z => z=x \/ z=y).
 Lemma cup_spec: forall x y z, Directed (fun z => z=x \/ z=y) -> cup x y <= z <-> (x <= z /\ y <= z).
 Proof.
   intros. unfold cup. rewrite sup_spec.
   now firstorder subst. apply H.
 Qed. (*small modif : need directedness in specification*)
  Lemma cup_spec_lat: forall x y z, cup x y <= z <-> (x <= z /\ y <= z).
 Proof.
   intros. unfold cup. rewrite sup_spec_lat.
   now firstorder subst.
 Qed.

 Definition cap x y := sup (fun z => z<=x /\ z<=y).
 Lemma cap_spec: forall x y z, Directed (fun z => z<=x /\ z<=y) -> z <= cap x y <-> (z <= x /\ z <= y).
 Proof.
   intros w y z D. unfold cap. split.
   now intro H; split; rewrite H; apply sup_spec.
   intros. now apply leq_xsup. 
 Qed. (*dunno if this will still be useful*)
 Lemma cap_spec_lat: forall x y z, z <= cap x y <-> (z <= x /\ z <= y).
 Proof.
   intros. unfold cap. split.
   now intro H; split; rewrite H; apply sup_spec_lat.
   intros. now apply leq_xsup_lat. 
 Qed.
*)


(* --------------- Inf ---------------- *)

(* Now defining an inf is also a problem... Usually we write it as the sup of elements lower than the set,
but now there is no guarantee an inf exists (even if a sup exists btw).
Two solutions : 
1) Define the inf directly in the CPO with "downward" directed sets
2) Define a "converse" CPO with reversed <= and define it as sup for this CPO.
--> Then we can make a lemma stating that the inf is actually the sup of lower elements 
if this set is downward directed. 
Try solution 2) to not "uselessly" weight down the definition of CPO.*)


 Definition inf Y := sup (fun z => forall y, Y y -> z <= y).
 Lemma inf_spec: forall Y z, Directed (fun z => forall y, Y y -> z <= y) -> z <= inf Y <-> (forall y, Y y -> z <= y).
 Proof.
   intros Y z D. unfold sup. split.
   intros H y Yy. rewrite H. apply sup_spec. now auto. 
   intro. now auto.
   intro. now apply leq_xsup. 
 Qed.
 Lemma inf_spec_lat: forall Y z, z <= inf Y <-> (forall y, Y y -> z <= y).
 Proof.
   intros. unfold sup. split.
   intros H y Yy. rewrite H; apply sup_spec_lat. now auto. 
   intro. now apply leq_xsup_lat.
 Qed.
 
  Lemma leq_xinf (D: X -> Prop) y: Directed (fun z : X => forall y0 : X, D y0 -> z <= y0) -> D y -> inf D <= y.
 Proof. intro H. now apply inf_spec. Qed.
 Lemma leq_xinf_lat (D: X -> Prop) y: D y -> inf D <= y.
 Proof. intro H. now apply inf_spec_lat with D. Qed.
 
 (** other properties of binary joins *)
 Lemma leq_xcup x y z: Directed (fun t => t=x \/ t=y) -> z <= x \/ z <= y -> z <= cup x y.
 Proof.
  intro D. Check cup_spec.
   destruct (cup_spec (cup x y) D).
   intros [E|E]; rewrite E; now apply H.
 Qed.
  Lemma leq_xcup_lat x y z: z <= x \/ z <= y -> z <= cup x y.
 Proof.
   destruct (cup_spec_lat x y (cup x y)) as [H _].
   now intros [E|E]; rewrite E; apply H.
 Qed.
 
 Lemma cup_l x y: Directed (fun t => t=x \/ t=y) -> x <= cup x y.
 Proof. auto using leq_xcup. Qed.
  Lemma cup_l_lat x y: x <= cup x y.
 Proof. auto using leq_xcup_lat. Qed.
 Lemma cup_r x y: Directed (fun t => t=x \/ t=y) -> y <= cup x y.
 Proof. auto using leq_xcup. Qed.
  Lemma cup_r_lat x y: y <= cup x y.
 Proof. auto using leq_xcup_lat. Qed.


(*Below is possible but not practical to write with directedness condition, 
do it later if needed*)
 Lemma cupA_lat x y z: cup x (cup y z) == cup (cup x y) z.
 Proof.
   apply from_above.
   intro. rewrite !cup_spec_lat. tauto.
 Qed.

 Lemma cupC x y: Directed (fun t => t=x \/ t=y) -> cup x y == cup y x.
 Proof.
   intro D.
   apply from_above.
   intro. rewrite !cup_spec. tauto.
   rewrite directed_symmetry. apply D. now setoid_rewrite or_comm at 1.
   apply D.
 Qed.
  Lemma cupC_lat x y: cup x y == cup y x.
 Proof.
   apply from_above.
   intro. rewrite !cup_spec_lat. tauto.
 Qed.

 Lemma or_reduce : forall A, A \/ A <-> A.
 Proof. tauto. Qed.
 Lemma cupI x: cup x x == x. (*done more generally with CPOs*)
 Proof.
   apply from_above.
   intro. rewrite !cup_spec. tauto.
   apply directed_symmetry with (fun z => z=x). (*intuition.*) now setoid_rewrite or_reduce.
   apply singleton_is_directed.
 Qed.

(* --- Inclusion of sets and includion of sups --- *)

Definition included (S T: X -> Prop) := forall x, S x -> T x.
Infix "⊆" := included (at level 70).

Lemma sup_preserves_inclusion S T : S ⊆ T -> Directed S -> Directed T -> sup S <= sup T.
Proof.
  intros H Ds Dt. apply sup_spec. assumption. intros. apply leq_xsup. assumption.
  now apply H.
Qed.

Lemma sup_preserves_eq S T : Directed S -> Directed T -> (forall x, S x <-> T x) -> sup S == sup T.
Proof.
  intros. apply weq_spec. split; apply sup_preserves_inclusion; 
  [intros x Hx | assumption | assumption | intros x Hx | assumption | assumption]; now apply H1.
Qed.

Lemma included_inf_is_greater S T : S ⊆ T 
  -> Directed (fun z : X => forall y : X, S y -> z <= y)
 -> Directed (fun z : X => forall y0 : X, T y0 -> z <= y0) 
 -> inf T <= inf S.
Proof.
  intros H Ds Dt. apply inf_spec. assumption. intros. apply leq_xinf. assumption.
  now apply H.
Qed.
Lemma inf_preserves_eq (S T : X -> Prop) : Directed (fun z : X => forall y : X, S y -> z <= y)
 -> Directed (fun z : X => forall y0 : X, T y0 -> z <= y0) -> (forall x, S x <-> T x) -> inf S == inf T.
Proof.
  intros. apply weq_spec. split; apply included_inf_is_greater; 
  [intros x Hx | assumption | assumption | intros x Hx | assumption | assumption]; now apply H1.
Qed.

End sup.
Global Hint Resolve bot_spec: core.
Global Hint Resolve cup_l cup_r: core.


Section functions.
 Context {X} {P: CPO X}.
 
 Record mon := { body:> X -> X; Hbody: Proper (leq ==> leq) body }.
 
 Global Instance Hbody' (F:mon) : Proper (weq ==> weq) F.
 Proof.
  apply (op_leq_weq_1 (Hf:=(Hbody F))).
Qed.


Inductive Image f (S : X -> Prop) : X -> Prop :=
  |from_image : forall x, S x -> Image f S (f x).

Definition Continuous φ := forall D, Directed D -> Directed (Image φ D)
   /\ φ (sup D) = sup (Image φ D).

Definition Increasing F := forall x, x <= F x.

Lemma mon_preserves_directedness_and_sup (F:mon) D : Directed D -> Directed (Image F D) /\ sup (Image F D) <= F (sup D).
Proof. intros.
  assert (Directed (Image F D)).
  + unfold Directed. intros. inversion H0. inversion H1.
  destruct (H x0 x1); try assumption. exists (F x2).
  repeat split; try apply Hbody; apply H6.
  + split. assumption. apply sup_spec. assumption. intros.
    inversion H1. apply Hbody. now apply leq_xsup.
Qed.


End functions.





(* Going on to Knaster-Tarski Theorem *)

Section lattice_results.
Context {X} `{L: CompleteLattice X}.
 Variable b: mon.

 Definition gfp := sup (fun x => x <= b x).

 Proposition leq_gfp: forall y, y <= b y -> y <= gfp.
 Proof. apply leq_xsup_lat. Qed.

 Lemma gfp_pfp: gfp <= b gfp.
Proof.
  unfold gfp. apply sup_spec_lat. intros y H. rewrite H. apply Hbody.
  apply leq_xsup_lat. apply H.
Qed.

 Lemma gfp_fp: gfp == b gfp.
Proof.
  rewrite weq_spec. split.
    + apply gfp_pfp.
    + apply leq_xsup_lat. apply Hbody. apply gfp_pfp.
Qed.

End lattice_results.





Section fixpoint.
 Context {X} {P: CPO X}.

 Definition Fix F (x:X) := F x == x.
 Definition Post F (x:X) := x <= F x.
 Definition Pre F (x:X) := F x <= x.
 
 Lemma fix_is_post F : forall x, Fix F x -> Post F x.
 Proof. intros. apply weq_spec in H. apply H. Qed.
 Lemma fix_is_pre F : forall x, Fix F x -> Pre F x.
 Proof. intros. apply weq_spec in H. apply H. Qed.
 
 Notation µ F := (inf (fun x => Fix F x)). (*Rmq : Attention, on préférerait que ce soit un min.
 Cependant, s'il existe, il est égal à l'inf donc c'est bon.*)
 
 Definition mu_exists F := Directed (fun z => forall y, (fun x => Fix F x) y -> z <= y) /\ Fix F (µ F).
 
 Fixpoint itere F n x0 : X := match n with
  | 0 => x0
  | S m => F (itere F m x0)
 end.

Lemma itere_monotony (F:mon) : forall n, Proper (leq ==> leq) (itere F n).
Proof.
  intros n x y H. induction n. now cbn. cbn. now apply Hbody.
Qed.

(*
 Inductive iteres F : X -> Prop :=
  | iteres_0 : (iteres F bot)
  | iteres_S : forall x, (iteres F x) -> (iteres F (F x)).
*)

Lemma chain_itere (F:mon) : forall (n : nat), itere F n bot <= itere F (S n) bot.
Proof.
  intro n. induction n. now cbn.
  cbn. now apply Hbody.
Qed.

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


(* This is already done by "inversion" on a <= *)
(*
Lemma inf_eq : forall (n m : nat), le n m -> n = m \/ le (S n) m.
Proof. 
  intros. inversion H. now left.
  right. now apply le_n_S.
Qed.
*)

(*3 lemmas below are actually useless, see le_ge_dec...
(Plus they already exist in Arith...)*)
Lemma compare_eq: forall e f, Nat.compare e f = Eq -> e=f.
Proof.
  induction e; destruct f; cbn; try discriminate.
  - reflexivity.
  - intro H. now rewrite IHe with f.
Qed.

Lemma compare_Lt: forall n m, Nat.compare n m = Lt -> n < m.
Proof. 
induction n; destruct m; cbn; try discriminate; intro H.
  + lia.
  + assert (n < m). now apply IHn. lia.
Qed.

Lemma compare_Gt: forall n m, Nat.compare n m = Gt -> m < n.
Proof. 
induction n; destruct m; cbn; try discriminate; intro H.
  + lia.
  + assert (m < n). now apply IHn. lia.
Qed.

(*
Lemma comparison : forall (n m:nat), le n m \/ le m n.
Proof. intros n m. case_eq
*)

Lemma iteres_directed (F:mon): Directed (iteres F).
Proof.
  unfold Directed. intros. destruct H. destruct H0.
  case_eq (Nat.compare n n0); intro H.
  + exists (itere F n bot). repeat split. easy. now rewrite compare_eq with n n0.
  + exists (itere F n0 bot). repeat split. apply chain_increase. 
  assert (n < n0). now apply compare_Lt. lia. reflexivity.
  + exists (itere F n bot). repeat split. reflexivity.
  apply chain_increase. assert (n0 < n). now apply compare_Gt. lia.
  Restart. unfold Directed. intros. destruct H. destruct H0.
  destruct le_ge_dec with n n0.
  + exists (itere F n0 bot). repeat split. now apply chain_increase. reflexivity.
  + exists (itere F n bot). repeat split. reflexivity. now apply chain_increase.
Qed.



 Notation α F := (sup (iteres F)).

 Theorem Fixpoint_I_i (F:mon) : Fix F (α F) -> mu_exists F /\ α F == µ F.
 Proof.
 intro H. 
 assert (forall β, Fix F β -> α F <= β). (*alpha is the least fixpoint.*)
  intros. apply sup_spec. apply iteres_directed. intros y Q.
  inversion Q. rewrite <- (itere_preserves_fix F β n).
  now apply itere_monotony. assumption.
 assert (Directed (fun z : X => forall y : X, Fix F y -> z <= y)). (*mu is well defined*)
    unfold Directed. intros. exists (α F). repeat split. intros. now apply H0.
    now apply H1. now apply H2.
  assert (α F == µ F). apply weq_spec. split.
   - apply inf_spec. apply H1. assumption.
   - apply leq_xinf. apply H1. assumption.
   - unfold mu_exists. repeat split. assumption.
    unfold Fix. rewrite <- H2. apply H. assumption.
Qed.




(* ---------------------- Theorem I (ii) ---------------------------------- *)

Inductive iteres_from_1 F : X -> Prop := 
  | from_bot_from_1 : forall n,  le 1 n -> iteres_from_1 F (itere F n bot).
  
Lemma iteres_from_1_directed (F:mon): Directed (iteres_from_1 F).
Proof.
  unfold Directed. intros. destruct H. destruct H0.
  destruct le_ge_dec with n n0.
  + exists (itere F n0 bot). repeat split. assumption. now apply chain_increase. reflexivity.
  + exists (itere F n bot). repeat split. assumption. reflexivity. now apply chain_increase.
Qed.

Lemma image_of_iteres F : forall x, (Image F (iteres F)) x <-> (iteres_from_1 F) x.
Proof.
  intro. split; intro; inversion H. inversion H0.
  + assert (iteres_from_1 F (itere F (S n) bot)). apply from_bot_from_1. lia.
    apply H3.
  + induction n. contradict H0. lia.
    cbn. apply from_image. apply from_bot.
Qed.

Lemma from_1_included F : included (iteres_from_1 F) (iteres F).
Proof.
  intros x H. inversion H. apply from_bot.
Qed.

Lemma sup_from_1 (F:mon) : α F == sup (iteres_from_1 F).
Proof.
  apply weq_spec. split. 
  + apply sup_spec. apply iteres_directed. intros. inversion H.
  induction n. now cbn.
  apply leq_xsup. apply iteres_from_1_directed.
  apply from_bot_from_1. lia.
  + apply sup_preserves_inclusion. apply from_1_included.
  apply iteres_from_1_directed. apply iteres_directed.
Qed.

(* Fix F (mu F) is here to say that "mu F exists", cause it is supposed to be a min and not an inf. *)
Theorem Fixpoint_I_ii (F:mon) : Continuous F -> mu_exists F /\ α F == µ F.
Proof.
  intro H. assert (Fix F (α F)).
  + unfold Fix. destruct H with (iteres F). apply iteres_directed. rewrite H1.
  transitivity (sup (iteres_from_1 F)). apply sup_preserves_eq. assumption. 
  apply iteres_from_1_directed. apply image_of_iteres. now rewrite sup_from_1.
  + now apply Fixpoint_I_i.
Qed.



(* ------------------------- Theorem II ------------------------------ *)

Notation µ0 F := (inf (fun x => Pre F x)). 

 Definition mu0_exists F := Directed (fun z => forall y, (fun x => Pre F x) y -> z <= y) /\ Pre F (µ0 F).
(*Warning : this is delicate. "If the least prefixpoint exists, we write it mu0" is not easily written in Coq.
I could also replace mu0_exists (and mu_exists) with the properties of a least prefixpoint, but to prove it from
the def of the inf I would still need the inf to be well defined, ie. this set to be directed.
I think it could be possible for this set to NOT be directed (so inf not well defined), but for such a least prefixpoint
to still exist. In that case I will not know how to define it at all. It will just be a "exists" proposition.*)

Lemma Induction_Rule (F:mon) : mu0_exists F -> mu_exists F /\ forall x, Pre F x -> µ F <= x.
Proof.
  intro H. destruct H.
  assert (Fix F (µ0 F)).
    apply weq_spec. split. apply H0.
    apply leq_xinf. assumption. unfold Pre. apply Hbody. apply H0.
  
  assert (Directed (fun z : X => forall y : X, Fix F y -> z <= y)).
    unfold Directed. intros. exists (µ0 F). repeat split. intros.
    apply leq_xinf. assumption. now apply fix_is_pre.
    now apply H2. now apply H3.
  
  assert (µ F == µ0 F).
    apply weq_spec. split. apply leq_xinf; assumption.
    apply included_inf_is_greater; try assumption. intros x Hx. now apply fix_is_pre.
  
  repeat split.
  + assumption.
  + unfold Fix. rewrite H3. apply H1.
  + intros. rewrite H3. apply leq_xinf; assumption.
Qed.




(* Lemma 8.21*)

Program Definition const x: mon := {| body y := x |}.
 Next Obligation. intros ? ? ?. reflexivity. Qed.

 (** identity and composition
     the monotonicity proofs are transparent to get strong equalities
     - [id ° f = f ° id = f], and
     - [f ° (g ° h) = (f ° g) ° h]
  *)
 Definition id: mon := {| 
   body x := x; 
   Hbody x y H := H 
 |}.

 Definition comp (f g: mon): mon := {|
   body := fun x => f (g x); 
   Hbody x y H := Hbody f _ _ (Hbody g _ _ H) 
 |}.
 Infix "°" := comp (at level 20): CPO.
 


Global Program Instance CPO_mon: CPO mon := {|
   weq := pointwise_relation X weq;
   leq := pointwise_relation X leq;
   sup F := {| body a := sup (fun b => exists2 f, F f & b=f a) |};
 |}.
 Next Obligation.
   intros x y H. apply sup_spec.
   unfold Directed. intros. destruct H0 as [f1 Ff1 f1x0]. destruct H1 as [f2 Ff2 f2y0].
   exists (f2 x). repeat split. now exists f2.
   
   intros i [f Ff ->].
   rewrite H. apply leq_xsup. eauto. 
 Qed.
 Next Obligation. constructor. now intros f x. intros f g h H H' x. now transitivity (g x). Qed.
 Next Obligation. unfold pointwise_relation. setoid_rewrite weq_spec. firstorder. Qed.
 Next Obligation.
   unfold pointwise_relation. setoid_rewrite sup_spec.
   firstorder. rewrite H1. auto. 
 Qed.


 Record mon_inc := { Ibody:> X -> X; HMbody: Proper (leq ==> leq) Ibody; HIbody : Increasing Ibody}.
 
 Instance HIbody' (f: mon_inc): Proper (weq ==> weq) f.
 Proof. intros x y. rewrite 2weq_spec. now split; apply f. Qed.

 (** constant function *)
 Program Definition const x: mon_inc := {| Ibody y := x |}.
 Next Obligation. intros ? ? ?. reflexivity. Qed.

 (** identity and composition
     the monotonicity proofs are transparent to get strong equalities
     - [id ° f = f ° id = f], and
     - [f ° (g ° h) = (f ° g) ° h]
  *)
 Definition id: mon_inc := {| 
   Ibody x := x; 
   HMbody x y H := H;
   HIbody x := (reflexivity x)
 |}.

(*
 Definition comp (f g: mon_inc): mon_inc := {|
   body := fun x => f (g x); 
   Hbody x y H := Hbody f _ _ (Hbody g _ _ H) 
 |}.
 Infix "°" := comp (at level 20): lattice.
 *)
 
 (** monotone increasing endofunctions form a new CPO *)
 Global Program Instance CPO_increasing_mon: CPO mon_inc := {|
   weq := pointwise_relation X weq;
   leq := pointwise_relation X leq;
   sup F := {| Ibody a := sup (fun b => exists2 f, F f & b=f a) |};
 |}.
 Next Obligation.
   intros x y H. apply sup_spec. intros i [f Ff ->].
   rewrite H. apply leq_xsup. eauto. 
 Qed.
 Next Obligation. constructor. now intros f x. intros f g h H H' x. now transitivity (g x). Qed.
 Next Obligation. unfold pointwise_relation. setoid_rewrite weq_spec. firstorder. Qed.
 Next Obligation.
   unfold pointwise_relation. setoid_rewrite sup_spec.
   firstorder. rewrite H1. auto. 
 Qed.







Program Instance CPO_self_maps_mon :  CPO (X -> X) :=
  {| weq:=pointwise_relation X weq;
     leq:=pointwise_relation X leq;
     sup F a:=sup (fun b => exists2 f, F f & b=f a);
  |}.
Next Obligation. 
  constructor.
   now intros f x. 
   intros f g h H H' x. now transitivity (g x).
Qed.
Next Obligation. unfold pointwise_relation. setoid_rewrite weq_spec. firstorder. Qed.
Next Obligation.
  unfold pointwise_relation. setoid_rewrite sup_spec.
  firstorder. rewrite H1. now apply H. 
Qed.
(*below : a simpler version of lemma 8.21 used in theorem. Only need existence of a FixPoint.*)
Lemma increasing_has_fix_point (F:mon) : Increasing F -> Fix F (α F).
Proof.
  intro. unfold Fix. apply weq_spec. unfold Increasing in H. split.
  + Check sup_spec. apply sup_spec with (iteres F). apply iteres_directed. reflexivity. .
Qed.

End fixpoint.































 

(** * Concrete instances *)

(** Prop is a complete lattice *)
Program Instance CompleteLattice_Prop: CompleteLattice Prop :=
  {| weq:=iff;
     leq:=Basics.impl;
     sup Y:=exists2 P, Y P & P;
  |}.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

(** Functions into a complete lattice form a complete lattice *)
Program Instance CompleteLattice_fun {A X} {L: CompleteLattice X}: CompleteLattice (A -> X) :=
  {| weq:=pointwise_relation A weq;
     leq:=pointwise_relation A leq;
     sup F a:=sup (fun b => exists2 f, F f & b=f a);
  |}.
Next Obligation. 
  constructor.
   now intros f x. 
   intros f g h H H' x. now transitivity (g x).
Qed.
Next Obligation. unfold pointwise_relation. setoid_rewrite weq_spec. firstorder. Qed.
Next Obligation.
  unfold pointwise_relation. setoid_rewrite sup_spec.
  firstorder. rewrite H1. now apply H. 
Qed.




(** * The complete lattice of monotone endofunctions *)

Section mon. 
 Context {X} {L: CompleteLattice X}.
 
 (** monotone endofunctions *)
 Record mon := { body:> X -> X; Hbody: Proper (leq ==> leq) body }.
 
 (** the following instances are not global: more powerful ones are 
    given at the end of the section *)
 Existing Instance Hbody.
 Instance Hbody' (f: mon): Proper (weq ==> weq) f.
 Proof. intros x y. rewrite 2weq_spec. now split; apply f. Qed.

 (** constant function *)
 Program Definition const x: mon := {| body y := x |}.
 Next Obligation. intros ? ? ?. reflexivity. Qed.

 (** identity and composition
     the monotonicity proofs are transparent to get strong equalities
     - [id ° f = f ° id = f], and
     - [f ° (g ° h) = (f ° g) ° h]
  *)
 Definition id: mon := {| 
   body x := x; 
   Hbody x y H := H 
 |}.

 Definition comp (f g: mon): mon := {|
   body := fun x => f (g x); 
   Hbody x y H := Hbody f _ _ (Hbody g _ _ H) 
 |}.
 Infix "°" := comp (at level 20): lattice.
 
 (** monotone endofunctions form a new complete lattice *)
 Global Program Instance CompleteLattice_mon: CompleteLattice mon := {|
   weq := pointwise_relation X weq;
   leq := pointwise_relation X leq;
   sup F := {| body a := sup (fun b => exists2 f, F f & b=f a) |};
 |}.
 Next Obligation.
   intros x y H. apply sup_spec. intros i [f Ff ->].
   rewrite H. apply leq_xsup. eauto. 
 Qed.
 Next Obligation. constructor. now intros f x. intros f g h H H' x. now transitivity (g x). Qed.
 Next Obligation. unfold pointwise_relation. setoid_rewrite weq_spec. firstorder. Qed.
 Next Obligation.
   unfold pointwise_relation. setoid_rewrite sup_spec.
   firstorder. rewrite H1. auto. 
 Qed.

 Global Instance comp_leq: Proper (leq ==> leq ==> leq) comp.
 Proof. intros f f' Hf g g' Hg x. simpl. rewrite (Hg x). apply Hf. Qed.
 Global Instance comp_weq: Proper (weq ==> weq ==> weq) comp := op_leq_weq_2.

 Lemma compA f g h: f ° (g ° h) = (f ° g) ° h.
 Proof. reflexivity. Qed.
 Lemma compIx f: id ° f = f.
 Proof. now case f. Qed. 
 Lemma compxI f: f ° id = f.
 Proof. now case f. Qed. 

End mon.
Arguments mon X {L}.
Infix "°" := comp (at level 20): lattice.

(** application as a function [X->X]->X->X is monotone in its two arguments *)
Instance app_leq {X} {L: CompleteLattice X}: Proper (leq ==> leq ==> leq) body.
Proof. intros f g fg x y xy. transitivity (f y). now apply f. now apply fg. Qed.
Instance app_weq {X} {L: CompleteLattice X}: Proper (weq ==> weq ==> weq) body := op_leq_weq_2.


(** * Knaster-Tarski *)
Section s.
    
 Context {X} {L: CompleteLattice X}.
 Variable b: mon X.

 Definition gfp := sup (fun x => x <= b x).

 Proposition leq_gfp: forall y, y <= b y -> y <= gfp.
 Proof. apply leq_xsup. Qed.

 Lemma gfp_pfp: gfp <= b gfp.
Proof.
  unfold gfp. apply sup_spec. intros y H. rewrite H. apply Hbody.
  apply leq_xsup. apply H.
Qed.

 Lemma gfp_fp: gfp == b gfp.
Proof.
  rewrite weq_spec. split.
    + apply gfp_pfp.
    + apply leq_xsup. apply Hbody. apply gfp_pfp.
Qed.


(** * Compatibility *)

 (** ** compatible functions *)
 Notation compat f := (f ° b <= b ° f) (only parsing).
 
 (** compositionality properties of compatibility *)
 Lemma compat_id: compat id.
Proof. reflexivity. Qed.
 
 Lemma compat_comp f g: compat f -> compat g -> compat (f ° g).
Proof. intros H1 H2. rewrite compA. rewrite <- H1. rewrite <- !compA. rewrite H2. reflexivity. Qed.

 Lemma compat_b: compat b.
Proof. reflexivity. Qed.

 Lemma compat_const y: y <= b y -> compat (const y).
Proof. intro H. intro x. simpl. apply H. Qed.
 
 Lemma compat_sup (F: mon X -> Prop):
   (forall f, F f -> compat f) -> compat (sup F).
Proof. intros H x. simpl. rewrite sup_spec. intros y Q. destruct Q as [f Q1 Q2].
  rewrite Q2. (* ici rewrite (H f). ne marche pas car il semble incapable de reconnaitre f (b x)*)
  assert (f (b x) = (f ° b) x).
    + simpl. reflexivity.
    + rewrite H0. rewrite (H f). (* je peux enfin le faire ! *)
      - simpl. apply Hbody. rewrite -> (leq_xsup (fun b0 : X => exists2 f0 : mon X, F f0 & b0 = f0 x)).
        reflexivity. exists f. apply Q1. reflexivity.
      - apply Q1.
Qed.


 (** compatible closures provide upto techniques *)
 Proposition upto f:
   compat f -> id <= f -> f ° f <= f ->
   forall x, x <= b (f x) -> x <= gfp.
Proof.
  intros H1 H2 H3 x H5. transitivity (f(x)). apply H2.
  apply leq_gfp. rewrite H5 at 1.
  assert (f (b (f x)) = (f ° b) (f x)). easy.
  rewrite H. rewrite H1.
  assert ((b ° f) (f x) = (b ° (f ° f)) x). easy.
  rewrite H0. rewrite H3. reflexivity.
Qed.

(** * Companion *)

 (** the companion is the largest compatible function *)
 Definition t := sup (fun f => compat f).

 Lemma compat_t: compat t.
 Proof. now apply compat_sup. Qed.

 (** more properties about [t] *)
 Lemma leq_t: forall f, compat f -> f <= t.
 Proof. apply leq_xsup. Qed.
 
 Lemma id_t: id <= t.
Proof. apply leq_t. reflexivity. Qed.

 Lemma b_t: b <= t.
Proof. apply leq_t. apply compat_b. Qed.

 Lemma tt_t: t ° t <= t.
Proof. apply leq_t.
  rewrite compA. rewrite <- compat_t. rewrite <- !compA. rewrite compat_t. reflexivity.
Qed.

 Lemma t_idem: t ° t == t.
Proof.
  rewrite weq_spec. split. apply tt_t.
  assert ((id°t) <= t ° t). rewrite id_t. reflexivity. rewrite <- H. reflexivity.
Qed.

 (** enhanced coinduction principle *)
 Definition bt := b ° t.
 Lemma coinduction x: x <= bt x -> x <= gfp.
Proof.
  intro H. apply upto with t.
  + apply compat_t.
  + apply id_t.
  + apply tt_t.
  + apply H.
Qed.


 (** characterisation of the greatest fixpoint via the companion *)
 Proposition gfp_tbot : gfp == t bot.
apply from_above. intro. split.
  + intro. apply sup_spec. intros. destruct H0 as [f ? ?]. rewrite <- H. apply leq_gfp.
    rewrite H1. assert ((b (f bot)) =(b ° f) bot). easy. rewrite H2. rewrite <- H0. simpl.
    apply Hbody. easy.
  + intro H. apply sup_spec. intros y H0. rewrite <- H. apply leq_xsup. exists (const y).
    - apply compat_const. apply H0.
    - simpl. reflexivity.
Qed.
 
 (** to sum up: [gfp = t bot = t gfp <= t x] *)
 Corollary t_gfp: t gfp == gfp.
Proof. 
  rewrite weq_spec. split.
  + rewrite gfp_tbot at 1. assert (t (t bot) = (t ° t) bot) as H0. easy.
   rewrite H0. rewrite tt_t. rewrite gfp_tbot. reflexivity.
  + assert ((t bot) <= (t gfp)). apply Hbody. easy. rewrite gfp_tbot at 1. apply H.
Qed.

 Corollary gfp_t x: gfp <= t x.
Proof.
  transitivity (t bot). rewrite gfp_tbot. reflexivity.
  apply Hbody. easy.
Qed.





(* Homework questions to do on paper or in Coq*)


(* Q1. Prove existence of a least fix point*)

 Definition lfp := inf (fun x => b x <= x). (*this will be proven a least fix point*)

 Lemma leq_xinf (P: X -> Prop) y: P y -> inf P <= y.
 Proof. now apply inf_spec. Qed.

 Proposition leq_lfp: forall y, b y <= y -> lfp <= y.  (*thus all fix points are greater than lfp*)
 Proof. apply leq_xinf. Qed.

 Lemma lfp_pfp:  b lfp <= lfp.
Proof.
  apply inf_spec. intros y H. rewrite <- H. apply Hbody.
  apply leq_xinf. apply H.
Qed.

 Lemma lfp_fp: lfp == b lfp. (*and lfp is indeed a fixpoint. CQFD Q1.*)
Proof.
  rewrite weq_spec. split.
  + apply leq_xinf. apply Hbody. apply lfp_pfp.
  + apply lfp_pfp.
Qed.



(* Q2. Prove compatibility of f\/g from compatibility of f and g.*)
Lemma cup_comp f g h: cup f g ° h == cup (f ° h) (g ° h). Admitted.

Lemma cup_preserve (z : mon X) (t : mon X) : forall (x : mon X) (y : mon X), x <= z -> y <= t -> cup x y <= (cup z t).
Proof.
  intros x y H Q. apply cup_spec. split.
  + rewrite H. apply leq_xsup. left. reflexivity.
  + rewrite Q. apply leq_xsup. right. reflexivity.
Qed.

Lemma meet_compat : forall f g, compat f -> compat g -> compat (cup f g).
Proof.
  intros. rewrite cup_comp. rewrite (cup_preserve H H0). rewrite cup_spec. split.
  + assert (f <= cup f g). - apply leq_xsup. left. reflexivity. 
    - rewrite <- H1. reflexivity.
  + assert (g <= cup f g). - apply leq_xsup. right. reflexivity. 
    - rewrite <- H1. reflexivity.
Qed.








