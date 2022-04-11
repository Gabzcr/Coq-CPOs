From Coq Require Import Arith.
(*Require Import Psatz.*)
(*Require Export Setoid Morphisms.*)
Import Coq.Lists.List.
Set Implicit Arguments.


Require Import Coq.Logic.FunctionalExtensionality.

Record fin X := {
  eq_dec : forall (a b : X), {a = b} + {a <> b};
  el : list X;
  all_el : forall a, List.In a el
  }.


Definition eq_bool A (Afin : fin A) x y := match (eq_dec Afin x y) with
  | left _ => true
  | right _ => false
  end.
  
Program Definition bool_fin : fin bool := {| el := cons true (cons false nil) |}.
Next Obligation. destruct a; destruct b. now left. now right. now right. now left. Qed.
Next Obligation. destruct a. now left. right. now left. Qed.


Section Finite.

Context {A B : Type} {Afin : fin A} {Bfin : fin B}.


(* ----- First "easier" version : functions from A to bool ----- *)

Fixpoint build_set X (X_eq_dec : forall (a b : X), {a = b} + {a <> b}) (l : list X) : list (X -> bool) := match l with
    | nil => cons (fun _ => false) nil
    | a::q => let r := build_set X_eq_dec q in 
      (List.map (fun h b => match (X_eq_dec a b) with
        | left _ => false
        | right _ => h b
        end) r ++ 
      List.map (fun h b => match (X_eq_dec a b) with
        | left _ => true
        | right _ => h b
        end) r)
  end.

Lemma In_is_decidable : forall (l : list A) (a : A), {In a l} + {~ (In a l)}.
Proof. intros. pose proof (all_el Afin). induction l. right. intro. contradict H0.
  destruct (eq_dec Afin a a0). left. now left. destruct IHl. left. now right. right.
  Search (~ _ \/ _). intro. destruct H0. symmetry in H0. now contradict H0. now contradict H0.
Qed.

Definition Ffalse a := (fun (h : A -> bool) (b : A) =>
      if eq_dec Afin a b then false else h b).
      
Definition Ftrue a := (fun (h : A -> bool) (b : A) =>
      if eq_dec Afin a b then true else h b).

Program Definition funAbool : fin (A -> bool) := {| el := build_set (eq_dec Afin) (el Afin) |}.
Next Obligation. Check List.forallb.
  destruct (List.forallb (fun x => eq_bool bool_fin (a x) (b x)) (el Afin)) eqn : EQ.
  (*destruct (eq_dec bool_fin true (List.forallb (fun x => eq_bool bool_fin (a x) (b x)) (el Afin))).*)
  + left. apply functional_extensionality. rewrite forallb_forall in EQ.
  intro. specialize EQ with x. pose proof (all_el Afin). apply EQ in H. unfold eq_bool in H.
  Search (if _ then _ else _). destruct (eq_dec bool_fin (a x) (b x)) eqn : AB. assumption. contradict H.
  intuition.
  + right. intro. assert (forall x, a x = b x). intro. now rewrite H. contradict EQ. Search (_ <> false).
    apply Bool.not_false_iff_true. apply forallb_forall. intro x. intro. unfold eq_bool.
    destruct (eq_dec bool_fin (a x) (b x)). easy. contradict n. apply H0.
Qed.
Next Obligation. assert (forall l f, (forall x, f x = match In_is_decidable l x with 
  | left _ => f x
  | right _ => false
  end) -> In f (build_set (eq_dec Afin) l)).
  induction l; cbn. intros. left. apply functional_extensionality. intro.
  specialize H with x. destruct (In_is_decidable nil x). contradict i. now symmetry.
  intros. apply in_or_app. destruct (eq_dec bool_fin (f a0) true).
  + right. assert (f = (Ftrue a0 (fun x => match In_is_decidable l x with 
    | left _ => f x
    | right _ => false
    end))). apply functional_extensionality. intro. unfold Ftrue.
    destruct (eq_dec Afin a0 x). now rewrite <- e0.
    destruct (In_is_decidable l x). easy. specialize H with x.
    destruct (In_is_decidable (a0 :: l) x ). destruct i. now contradict H0. now contradict H0.
    assumption.
    
    rewrite H0. apply in_map. apply IHl. intros. now destruct (In_is_decidable l x).
  + left. assert (f = (Ffalse a0 (fun x => match In_is_decidable l x with 
    | left _ => f x
    | right _ => false
    end))). apply functional_extensionality. intro. unfold Ffalse.
    destruct (eq_dec Afin a0 x). rewrite <- e. destruct (f a0). contradict n. easy. easy.
    destruct (In_is_decidable l x). easy. specialize H with x.
    destruct (In_is_decidable (a0 :: l) x ). destruct i. now contradict H0. now contradict H0.
    assumption.
    
    rewrite H0. apply in_map. apply IHl. intros. now destruct (In_is_decidable l x).
  
  + apply H. intro. destruct (In_is_decidable (el Afin) x). easy. 
    contradict n. apply (all_el Afin).
Qed.



(* ------- More general version : function from any finite set to any finite set ------- *)


Definition empty C (Cfin : fin C) := (el Cfin = nil).

Definition empty_fun {C D} {Cfin : fin C} : @empty C Cfin -> (C -> D).
Proof. intros H x. pose proof (all_el Cfin). rewrite H in H0. contradict (H0 x). Qed.

Lemma empty_fun_ind_of_proof {C} {Cfin : fin C} (D : Type) : forall (H1 H2 : @empty C Cfin), 
  empty_fun (D := D) H1 = empty_fun H2.
  Proof. intros. apply functional_extensionality. intro. pose proof (all_el Cfin).
  rewrite H1 in H. contradict (H x). Qed.

Fixpoint add_last_image A B (A_eq_dec : forall (a b : A), {a = b} + {a <> b})
                            (B_eq_dec : forall (a b : B), {a = b} + {a <> b})
                            (l : list B) (previous_res : list (A -> option B)) (last_element : A)
                             : list (A -> option B) :=
  match l with
    | nil => nil
    | b :: q => List.map (fun h a => match (A_eq_dec last_element a) with
        | left _ => Some b
        | right _ => h a
        end) previous_res ++ add_last_image A_eq_dec B_eq_dec q previous_res last_element
  end.

Fixpoint build_fun_opt A B (A_eq_dec : forall (a b : A), {a = b} + {a <> b})
                       (B_eq_dec : forall (a b : B), {a = b} + {a <> b})
                       (lA : list A) (lB : list B) 
                       : list (A -> option B) 
    := match lA with
        | nil => cons (fun _ => None) nil
        | a::q => let r := build_fun_opt A_eq_dec B_eq_dec q lB in
                  add_last_image A_eq_dec B_eq_dec lB r a
        end.

Definition retrieve_option C D default (h : C -> option D) x := match (h x) with
                | None => default (* This case doesn't happen, just need the type to be correct *)
                | Some d0 => d0
                end.

Program Definition build_fun C D (Cfin : fin C) (Dfin : fin D)
                       : list (C -> D)
  := match (el Dfin) with
    | nil => (match (el Cfin) as l return (el Cfin = l) -> list (C -> D) with
            | nil => (fun Heq =>  cons (@empty_fun C D Cfin Heq) nil)
            | c :: qc => fun _ => nil
            end) eq_refl
    | d :: qd => List.map (retrieve_option d) (build_fun_opt (eq_dec Cfin) (eq_dec Dfin) (el Cfin) (el Dfin))
    end.

Definition F_opt C im pre := (fun (h : A -> C) (a : A) =>
      if eq_dec Afin pre a then im else h a).


Program Definition funAB : fin (A -> B) := {| el := build_fun Afin Bfin |}.
Next Obligation. Check List.forallb.
  destruct (List.forallb (fun x => eq_bool Bfin (a x) (b x)) (el Afin)) eqn : EQ.
  (*destruct (eq_dec bool_fin true (List.forallb (fun x => eq_bool bool_fin (a x) (b x)) (el Afin))).*)
  + left. apply functional_extensionality. rewrite forallb_forall in EQ.
  intro. specialize EQ with x. pose proof (all_el Afin). apply EQ in H. unfold eq_bool in H.
  Search (if _ then _ else _). destruct (eq_dec Bfin (a x) (b x)) eqn : AB. assumption. contradict H.
  intuition.
  + right. intro. assert (forall x, a x = b x). intro. now rewrite H. contradict EQ. Search (_ <> false).
    apply Bool.not_false_iff_true. apply forallb_forall. intro x. intro. unfold eq_bool.
    destruct (eq_dec Bfin (a x) (b x)). easy. contradict n. apply H0.
Qed.
Next Obligation.
  induction (el Bfin) eqn : EQB.
  + induction (el Afin) eqn : EQA.
    - unfold build_fun. rewrite EQB.
      assert (empty Afin) as Em. apply EQA.

    assert ((fun Heq : el Afin = nil => empty_fun (D := B) Heq :: nil) 
        =  (fun _ : el Afin = nil => empty_fun Em :: nil)).
    apply functional_extensionality. intro. apply f_equal2.
    apply empty_fun_ind_of_proof. reflexivity.
    rewrite H. rewrite EQA.
    assert (a = empty_fun Em). apply functional_extensionality. intro.
    pose proof (all_el Afin). rewrite EQA in H0. contradict (H0 x).
    rewrite H0. apply in_eq.

    - pose proof (all_el Bfin). rewrite EQB in H. contradict (H (a a0)).

  + assert (forall l f, (forall x, match In_is_decidable l x with 
    | left _ => exists b, f x = Some b
    | right _ => f x = None
    end)
    -> In f (build_fun_opt (eq_dec Afin) (eq_dec Bfin) l (el Bfin))).
    induction l0; cbn.
    - intros. left. apply functional_extensionality. intro.
      specialize H with x. destruct (In_is_decidable nil x). contradict i. now symmetry.
    - intros. assert (f = (F_opt (f a1) a1 (fun x => match In_is_decidable l0 x with 
      | left _ => f x
      | right _ => None
      end))).
      apply functional_extensionality. intro. unfold F_opt.
      destruct (eq_dec Afin a1 x). now rewrite <- e.
      destruct (In_is_decidable l0 x). easy. specialize H with x.
      destruct (In_is_decidable (a1 :: l0) x). destruct i. now contradict H0.
      now contradict H0. assumption.
    
      assert (forall l_temp, (match f a1 with | Some b => In b l_temp |None => True end) ->  In f
       (add_last_image (eq_dec Afin) (eq_dec Bfin) l_temp
       (build_fun_opt (eq_dec Afin) (eq_dec Bfin) l0 (el Bfin)) a1)).
      ++ induction l_temp.
      * intro. pose proof (H a1). destruct (In_is_decidable (a1 :: l0) a1).
        destruct H2. rewrite H2 in H1. contradict H1.
        contradict n. apply in_eq.
      * intro. pose proof (H a1). destruct (In_is_decidable (a1 :: l0) a1).
        destruct H2. rewrite H2 in H1. destruct H1.
        ** unfold add_last_image. apply in_or_app. left.
          assert (F_opt (f a1) a1 = 
          (fun (h : A -> option B) (a3 : A) => if eq_dec Afin a1 a3 then Some a2 else h a3)).
          unfold F_opt. apply functional_extensionality. intro. apply functional_extensionality. intro.
          destruct (eq_dec Afin a1 x1). rewrite H2. now rewrite H1. easy.
          rewrite H0. rewrite <- H3. apply in_map. apply IHl0. intro. destruct (In_is_decidable l0 x0).
          pose proof (H x0). destruct (In_is_decidable (a1 :: l0) x0). apply H4. contradict n. now apply in_cons. easy.
        ** unfold add_last_image. apply in_or_app. right. apply IHl_temp. now rewrite H2.
       ** contradict n. apply in_eq.
      
      ++ apply H1. pose proof (H a1). destruct (In_is_decidable (a1 :: l0) a1).
        destruct H2. rewrite H2. apply (all_el Bfin). now rewrite H2.
      
     - unfold build_fun. rewrite EQB. assert (a = retrieve_option a0 (fun x => Some (a x))).
      apply functional_extensionality. intro. now cbn.
      rewrite H0. apply in_map. rewrite <- EQB. apply H. intro.
      destruct (In_is_decidable (el Afin) x). now exists (a x). contradict n. apply (all_el Afin).
Qed.

End Finite.
  
Section Application.

Context {A} {Afin : fin A}.

  Program Definition funAbool' : fin (A -> bool) := @funAB A bool Afin bool_fin.
  
  Program Definition funAA : fin (A -> A) := @funAB A A Afin Afin.

End Application.
  
  
Section SubType.

  Context {A} {Afin : fin A}.
  Variable P : A -> bool.
  
  Search true.
  
  Definition subAP := {a:A | Bool.Is_true (P a)}.
  
  Check List.filter.
  Print List.filter.
  
  Search Bool.Is_true.
  
  Program Fixpoint build_subset (l : list A) : list (subAP) := match l with
    | nil => nil
    | a :: l0 => let new_element := match P a as b return P a = b -> (list subAP) with
        | true => (fun H => cons (exist (fun x => Bool.Is_true (P x)) a (Bool.Is_true_eq_left (P a) H)) nil)
        | false => fun _  => nil
      end eq_refl
      in new_element ++ (build_subset l0)
  end.
  (*Next Obligation. now apply Bool.Is_true_eq_right. Qed.*)

(*Require Import Coq.Program.Equality.*)

Lemma test : forall b (p1 p2 : Bool.Is_true b), p1 = p2.
Proof.
  intro b. destruct b. intros. cbn in p1, p2. now destruct p1, p2.
  intros. cbn in *. contradiction.
Qed.

Lemma fold_proj : forall a, (exist (fun a0 : A => Bool.Is_true (P a0)) (proj1_sig a) (proj2_sig a)) = a.
Proof. intro. destruct a. cbn. reflexivity. Qed.

  Program Definition funP : fin subAP := {| el := build_subset (el Afin) |}.
  Next Obligation. destruct a as [a Pa]. destruct b as [b Pb].
   destruct (eq_dec Afin a b).
   + left. Search Bool.Is_true. induction e. Print Bool.Is_true.
   unfold Bool.Is_true in Pa, Pb. pose proof (test (P a) Pa Pb).
   rewrite <- H. reflexivity.
   + right. intro. inversion H. contradiction.
   Qed.
  Next Obligation.
    (*destruct a as [a Pa].*)
    assert (forall (l : list A) x, match (@In_is_decidable A Afin l (proj1_sig x)) (*as b return 
        (In_is_decidable l (proj1_sig x)) = b -> Prop*) with
      | left Px => In x (build_subset l)
      | right _ => True
      end).
    - intros l x. (*destruct x as [x Px]. cbn.*) destruct (In_is_decidable l (proj1_sig x)).
      -- induction l. contradict i. cbn. apply in_or_app.
         inversion i. left.
     
     
     
     assert (((if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H0 : P a0 = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H0)
     :: nil
    else fun _ : P a0 = false => nil) eq_refl) = ((if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H0 : P a0 = true =>
     x
     :: nil
    else fun _ : P a0 = false => nil) eq_refl)). 
    (*beginning of garbage*)
    
    
    assert ((if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H0 : P a0 = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H0)
     :: nil
    else fun _ : P a0 = false => nil) = (if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H0 : P a0 = true =>
     x
     :: nil
    else fun _ : P a0 = false => nil)).
    (*beginning of garbage of type 2 *)
    
    
     
     
         assert ((fun H0 : P a0 = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H0)
     :: nil) = fun H0 =>
     x
     :: nil).
     (*end of garbage of type 3 *)
     
     apply functional_extensionality. intro Pa0.
     assert (exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) Pa0) = x).
     
     destruct x. cbn in *. induction H. assert ((Bool.Is_true_eq_left (P a0) Pa0) = i0).
      apply test. now rewrite H.
     
     
     
     now rewrite H0.

     
     
   
     (*end of garbage of type 3 *)
     now rewrite H0.
         
     
     
     
     
     
     (*end of garbage of type 2 *)
     now rewrite H0.
    
    
    
    
    
    (*end of garbage*)
    setoid_rewrite H0. rewrite H. destruct (P (proj1_sig x)) eqn : EQ. apply in_eq.
    contradict EQ.
    rewrite (Bool.Is_true_eq_true (P (proj1_sig x)) (proj2_sig x)). apply Bool.diff_true_false.
    
    right. now apply IHl.
      -- easy.
    
    - specialize H with (el Afin) a. destruct (In_is_decidable (el Afin) (proj1_sig a)).
      assumption. contradict n. apply (all_el Afin).
 Qed.
    
    
    
    
    
    
     
     assert ((if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H0 : P a0 = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H0)
     :: nil
    else fun _ : P a0 = false => nil) = (if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H0 : P a0 = true =>
     x
     :: nil
    else fun _ : P a0 = false => nil)). admit. rewrite H0.
         
         assert ((fun H0 : P a0 = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H0)
     :: nil) = fun H0 =>
     x
     :: nil). admit. setoid_rewrite H0.
         
          destruct (P a0).
         

  (*
    rewrite H.
    
    
        assert (((if P (proj1_sig x) as b return (P (proj1_sig x) = b -> list subAP)
    then
     fun H0 : P (proj1_sig x) = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) (proj1_sig x)
       (Bool.Is_true_eq_left (P (proj1_sig x)) H0) :: nil
    else fun _ : P (proj1_sig x) = false => nil) eq_refl)
      = ((if P (proj1_sig x) as b return (P (proj1_sig x) = b -> list subAP)
    then
     fun H0 : P (proj1_sig x) = true =>
     x :: nil
    else fun _ : P (proj1_sig x) = false => nil) eq_refl)). 
    (*above is beginning of proof*)
    
    assert ((fun H0 : P (proj1_sig x) = true =>
  exist (fun x0 : A => Bool.Is_true (P x0)) (proj1_sig x)
    (Bool.Is_true_eq_left (P (proj1_sig x)) H0) :: nil) = fun H1 => x :: nil).
  apply functional_extensionality. intros.
  
  assert (exist (fun x1 : A => Bool.Is_true (P x1)) (proj1_sig x)
  (Bool.Is_true_eq_left (P (proj1_sig x)) x0) = x).
  
  destruct x. cbn in *. assert ((Bool.Is_true_eq_left (P x) x0) = i0). apply test.
  
     *)
     
     
     (*
         assert (((if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H1 : P a0 = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H1) :: nil
    else fun _ : P a0 = false => nil) eq_refl)
      = ((if P a0 as b return (P a0 = b -> list subAP)
    then
     fun H1 : P a0 = true =>
     x :: nil
    else fun _ : P a0 = false => nil) eq_refl)). 
    (*above is beginning of proof*)
    
    assert ((fun H1 : P a0 = true =>
  exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H1) :: nil) = fun H1 => x :: nil).
  apply functional_extensionality. intros.
  
  assert (exist (fun x1 : A => Bool.Is_true (P x1)) a0 (Bool.Is_true_eq_left (P a0) x0) = x).
  destruct x. cbn in *. admit. *)(*
  assert ((Bool.Is_true_eq_left (P a0) x0) = i0).
  admit.
  
  
  now rewrite H0.*)
  
  
  
  assert ((fun H0 : P a0 = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) a0 (Bool.Is_true_eq_left (P a0) H0)
     :: nil) = fun H1 => x :: nil).
  apply functional_extensionality. intros.
  
  assert (exist (fun x1 : A => Bool.Is_true (P x1)) a0 (Bool.Is_true_eq_left (P a0) x0) = x).
  
  destruct x. cbn in *. assert ((Bool.Is_true_eq_left (P a0) x0) = i0). apply test.
  
  
  
  
  
  now rewrite H0.
  
  now rewrite H0.
  
  
    
    (*Below is end of proof*)
    setoid_rewrite H0. rewrite fold_proj.
    
    
    
     (*destruct x. cbn in *.*)
    (*rewrite H.*) destruct (P (proj1_sig x)) eqn : EQ. 
    assert (exist (fun a1 : A => Bool.Is_true (P a1)) (proj1_sig x) (proj2_sig x) = x).
    apply fold_proj.
    rewrite H1. Search In. apply in_eq. contradict EQ.
    rewrite (Bool.Is_true_eq_true (P (proj1_sig x)) (proj2_sig x)). apply Bool.diff_true_false.
   
         
         
         (*
         assert ((fun H1 => exist (fun x0 : A => Bool.Is_true (P x0)) a0 (build_subset_obligation_1 H1)) = fun H => x).
         admit.
         setoid_rewrite H0.
         
         case (P a0). rewrite H. Search Bool.Is_true.
         assert ((fun H0 : P (proj1_sig x) = true =>
     exist (fun x0 : A => Bool.Is_true (P x0)) (proj1_sig x) (build_subset_obligation_1 H0) :: nil) 
     = (fun H0 : P (proj1_sig x) = true => x :: nil)). admit.
     setoid_rewrite H0.
     
         destruct (P (proj1_sig x)).
         pose proof (Bool.Is_true_eq_true (P x) Px). rewrite H0.*)
         right. now apply IHl.
      -- easy.
    
    - specialize H with (el Afin) a. destruct (In_is_decidable (el Afin) (proj1_sig a)).
      rewrite fold_proj in H. apply H. contradict n. apply (all_el Afin).
 Qed.
      
    (*
    pose proof (all_el Afin). induction (el Afin). contradict (H a).
    cbn. specialize H with a. inversion H.
    + admit.
    + Search In. apply in_or_app. right. apply IHl. destruct (P a0).
  Qed.
   
   
   
   assert (Pa = Pb).
   
    rewrite e.
   Search Bool.Is_true. 
   
   Search ({_=_} + {_<>_}).
  pose proof Eqdep_dec.UIP_dec as H. specialize H with bool (P a) true Pa' Pa'. apply (eq_dec Afin).
*)

End SubType.
  
  
  (* BROUILLON
  
  Définir les types finis dans un fichier à part comme ci-dessous
  
  Record fin X := {|
    eq_dec : forall a b, {a = b} + {a <> b};
    el : list A;
    all_ell : forall a, List.In a el
    |}.
    
  K = fin
  
  
  
  
  
  
  
  
  "list.filter" pour sélectionner selon une propriété --> autre chose
  
  match P a as b return P a = b -> (list {a | P a}) with
  | true => lambda H. [(a, H)]
  | false => lambda _ .[]
  end eq_refl.
  
  Rmq : proof irrelevance est vrai sur les booléens ! -> chercher le lemme associé !
  
  
  
  
  let rec f = function 
    | [] -> [lambda _ .false]
    | a::q -> let r = f q in List.map (lambda h b -> if a = b then false else h b) r ++ List.map (... true) r
    *)
  