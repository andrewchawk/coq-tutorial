Module CoqTutorial.

(* Xiaoning Bian, Dalhousie University *)

(* 
This tutorial contains:

1) Coq basics.
2) data types: Empty, Singleton, Bool, Nat, and List.
3) Equality data type.
4) Prove addition is associative.
5) Prove insertion sort is correct.

*)

(* 
References:
https://cel.hal.science/inria-00001173
https://cs.uwaterloo.ca/~plragde/flaneries/LACI/Proof_Assistants.html
https://people.cs.kuleuven.be/~bart.jacobs/coq-essence.pdf
https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html
*)


(* 
First of all, let's download and install CoqIDE. You can run this file in it.

For Windows and MacOS users, you can download from here,
https://www.mathstat.dal.ca/~xbian/uploads/softwares/

For Linux users, please run this command in your terminal:
sudo snap install coq-prover

Or refer to here,
https://snapcraft.io/coq-prover

*)


(*
We start with data types, and along the way, we also pick up some Coq basics.
For now, we just regard "type" as "set". Integers have type Int, and the conversely, the type Int is the set of all integers.
*)

(* Empty type or Empty set *) 
Inductive Empty : Set := .

(* In CoqIDE, press Ctrl + rightarrow to type-check things defined till the cursor, Ctrl + downarrow to type-check the next clause, Ctrl + uparrow to type-check the previous clause, and Ctrl + End to type-check the whole file. *)

(* Singleton type or Sinlgeton set *)
Inductive Singleton : Set := singleton.

(*
Question: these two are so simple, what use do they have?
Answer: a lot.
*)

(*
First of all, we can define several functions between two sets.
f0 : Empty -> Empty;
f1 : Empty -> Singleton;
f2 : Singleton -> Singleton;
 *)

Definition f2 : Singleton -> Singleton := fun (s : Singleton) =>
  match s with
    singleton => singleton
  end.

(* Alternative definitions. We will show f2 = f2a, f2 = f2b, f2 = f2c later. *)

Definition f2a (s : Singleton) : Singleton :=
  match s with
    singleton => singleton
  end.
Definition f2b (s : Singleton) : Singleton := s.
Definition f2c (s : Singleton) := s.


Definition f0 : (Empty -> Empty) := fun (m : Empty) =>
  match m with end.


(* Alternative definition. We will show f0 = f0a later. *)
Definition f0a : (Empty -> Empty) := fun (m : Empty) => m.

Definition f1 : (Empty -> Singleton) := fun (m : Empty) =>
  match m with end.

(*Can we define a function from Singleton to Empty? NO. *)

(*
Definition f4 (s : Singleton) :=
  match s with 
    singleton => ??
  end.
*)

(*
In fact, there is no function to Empty from any non-empty set. f0 is the only possible function to Empty.
*)

Inductive Bool : Set := true | false.

(* Boolean operatations: and, or, implies, xor, etc.. *)
Definition and (b1 : Bool) (b2 : Bool) : Bool := 
  match b1 with
    | true => match b2 with
              true => true
              | false => false
            end
    | false => false
  end.

(*exercise: define or, implies, xor. *)


(* Natural numbers starting from 0. *)
Inductive Nat : Set :=
  | zero : Nat
  | succ : Nat -> Nat.

(* Notations for first 10 numbers. *)
Notation "0" := zero.
Notation "1" := (succ zero).
Notation "2" := (succ 1).
Notation "3" := (succ 2).
Notation "4" := (succ 3).
Notation "5" := (succ 4).
Notation "6" := (succ 5).
Notation "7" := (succ 6).
Notation "8" := (succ 7).
Notation "9" := (succ 8).

(* Addition *)
Fixpoint add (m : Nat) (n : Nat) : Nat :=
  match m with 
    | zero => n
    | succ m' => succ (add m' n)
    end.

Check add.
Compute (add 4 5).

Notation "x + y" := (add x y) (at level 50, left associativity).

Compute (zero + zero + zero).
Compute (3 + 4).

(* We want to show add is associative, i.e., forall (a b c), a + (b + c) = (a + b) + c. *)

(* Note that, since we define + to be left assocative, (a + b) + c is exactly the same as a + b + c. *)

(* 
what is "forall" and what is "="?
In other words, how to express forall quantifier and equality in Coq?
 *)

(* 
The addition we defined is implicitly quantified by forall, since it says we can add any two natural number. In general, any function defined in Coq is total and hence forall quantified. This suggests that we should define associativity as a fucntion on a, b, c, which returns the "equal" property. E.g., something like this,
*)

(*
Definition assoc : Nat -> Nat -> Nat -> Equality Property
*)

(*
Instead, let use reserved word Theorem instead of Definition. In Coq, there is not much difference between the following keywords: Defintion; Lemma; Theorem; Example; Remark; Fact. The difference is mainly for documentation. Coq may treat them slightly differently, but not a lot.
*)

(*
Theorem assoc : Nat -> Nat -> Nat -> Equality Property
*)

(* The main problem is how to express equality property. *)

(* 
First try, since there is two possibilty, either equal or not equal,
maybe lets use Bool to indicate this. We can define a function tatking
two natural numbers, and if they are equal, it return "true", otherwise "false". 
*)

Fixpoint equalNB (a : Nat) (b : Nat) : Bool := 
    match a with
      | zero => match b with
              | zero => true
              | succ b' => false
              end
      | succ a' => match b with
              | zero => false
              | succ b' => equalNB a' b'
              end
      end.


(*
Theorem assoc : Nat -> Nat -> Nat -> equalNB (a + (b + c)) (a + b + c) = true.
Theorem assoc : Nat -> Nat -> Nat -> equalNB (a + (b + c)) (a + b + c) "always equals to" true.
*)

(*
Again, we need equality for Bool. Like for Nat, we can define equalilty test for Bool, easier than for Nat.
*)

Definition equalBB (a : Bool) (b : Bool) : Bool := 
    match a with
      | true => match b with
              | true => true
              | false => false
              end
      | false => match b with
              | true => false
              | false => true
              end
      end.  

(* 
We saw some redundancy there, awkwardly. But still, what does it mean by "always equals to"? The equality test functions we defined don't guarantee "always equality" obviously, since they might return false. This method might be enough for testing in software engineering. We have a test function, we just run thousands of test cases to see if we always get true return. It is not a proof. Also we have infinite many inputs, the test can never be complete.

The magical leap happens here (comparing to ordinary programming languages).

We know a fucntion "always" return a value when fed with an input. We might be able to use this feature to capture "always". We know for a function, there must be a domain and a codomain, in other words, an input type and an output type. Let the domain be (Nat x Nat x Nat), what is the codomain? A type about "equality". We need "equality type"!

Given natural numbers a b, we want a = b to be a type! not a test whether a equals b, but a type. Not a value, but a set, a type. We want that there exits a function from Nat x Nat x Nat to lhs = rhs, whenever lhs is equal to the rhs, and we want that there is no fucntion from Nat x Nat x Nat to lhs = rhs if they are not equal.

Recall, Empty is such that there is no function to it (excepty from Empty). So we define lhs = rhs to be Empty if lhs is not equal to rhs. I forgot to mention that there is always an unique function from any set to Singleton, which just map everything to singleton. Lets try to define lhs=rhs to be Singleton if lhs is equal to rhs.

To sum up, lhs=rhs is either Empty or Singleton, depending on what values lhs and rhs are. In other word, lhs=rhs is a family of types (either Empty or Singleton) parametered by lhs and rhs, which are value. Such a pattern, type family indexed by values of another type, is call "dependent type". Both Coq and Agda support dependent types. Dependent types are essential in proof assistant, since we are interested in showing some value satisfty some property, where property is a set or a type.

In summary, a function is powerful enough to express: 1) forall quantification; 2) "always" property, which will be expoited only if we have Equality type.

*)

Definition Equal' : Nat -> Nat -> Set := 
  fun (lhs : Nat) (rhs : Nat) =>
    match (equalNB lhs rhs) with
      | true => Singleton
      | false => Empty
    end.


Compute (Equal' 1 2).
Compute (Equal' 3 3).

(*
We are still using the test function, but we should be smarter than that. We have the equivalent defintion without using the test fucntion. 
*)

Inductive Equal (a : Nat) : Nat -> Set := 
  | refl : Equal a a.

(*
This type reads: 1) there is only one element in Equal a a for each a in Nat, so like Singleton, but not exactly Singleton; 2) there is no elment in Equal a b provided a is not equal to b, which is Empty.
*)

(* Let's make a Notation. Instead of = which is reserved, we use ==. *)

Notation "x == y" := (Equal x y) (at level 60, no associativity).

(* A property of equality. *)

Lemma Equal_context_succ : forall (x y : Nat), x == y -> succ x == succ y.
Proof.
intros x y H.
elim H.
exact (refl (succ x)).
Qed.

(* Now our assoc property becomes: *)

(*
Theorem assoc (a : Nat) (b : Nat) (c : Nat) : a + (b + c) == a + b + c.
*)

(* More informatively, *)

Theorem assoc : forall (a : Nat) (b : Nat) (c : Nat), a + (b + c) == a + b + c.

(* 
A proof of this theorem is just a fucntion from Nat x Nat x Nat to the type a + (b + c) == a + (b + c). Let's contruct it.
*)
Proof. 
intros a b c.
induction a as [ | a' ih].
  - simpl. exact (refl (b + c)).
  - simpl. rewrite ih. exact (refl (succ (a' + b + c)) ).
Qed.

(* Note that this proof is a little bit in Agda style. *)
(*
This is an Agda proof of associativity, copied from my thesis.

-- Associativity. Note that the induction hypothesis is a recursive
-- call of lemma-add-assoc on a structural smaller argument.
lemma-add-assoc : ∀ (x y z : ℕ) → (x + y) + z == x + (y + z)
lemma-add-assoc zero y z = refl
lemma-add-assoc (succ x) y z = context succ ih
  where
    ih = lemma-add-assoc x y z
*)


(* Now, let's verity insertion sort. *)

(* 
There are a lot to define:
  1) what are we sorting?
  2) what is the sorting according to?
  3) how to compare two natural number?
  4) what is insertion?
  5) what does correctness mean?
  etc..
*)

(* 
If we implement sorting in C, we will probably use array. In some other lauguage, it might be called Vector. One problem with that, vector or array always has a size or length, but we might have more things to sort than that length limitation.

In Coq, or Agda, Haskell, or any other language that supports infinite long list, things are more elegant. We just sort on a list. Nota that the difference between vector and list is that vector has a fixed length (however large it is, it is finite), but list can be of any size. Let's define List.
*)

Inductive ListNat : Set := 
  | nil : ListNat
  | con : Nat -> ListNat-> ListNat.

(* Let's make a notation for list. *)
Notation "h ; t" := (con h t) (at level 55, right associativity).

Compute (1;2;3;4; nil).
(* Note that we always have "nil" in any list to denote the ending. *)

Definition ObjectToSort := ListNat.

(* This solves the first question --- what to sort? *)

(*
Apparently, we are sorting according which is larger and which is smaller, we want to sort them from small to large. We are facing the same problem when we define equality. We need more than just a testing function. We want something like 1 < 2 being a set, a type, especially a singleton set. Very similar to equality, we define LessOrEqual as follows:
*)

Inductive LessOrEqual : Nat -> Nat -> Set :=
  | LEzero : forall (b : Nat), LessOrEqual zero b
  | LEsucc : forall (a b : Nat), LessOrEqual a b -> LessOrEqual (succ a) (succ b).

Notation "x =< y" := (LessOrEqual x y) (at level 60, no associativity).

Definition Less (a b : Nat) : Set := succ a =< b.

Notation "x <' y" := (Less x y) (at level 60, no associativity).

(* Some properties of Less and LessOrEqual. *)

Lemma x_le_xplus1 : forall (x : Nat), x =< succ x.
Proof.
intro x.
induction x.
  - exact (LEzero 1).
  - exact (LEsucc _ _ IHx).
Qed.

Lemma zero_less_succ : forall (x : Nat), zero <' succ x.
Proof.
induction x.
  - exact (LEsucc (zero) (zero) (LEzero zero)).
  - exact (LEsucc (zero) (succ x) (LEzero (succ x))).
Qed.


Definition LEsucc_inv (x y : Nat) (H : succ x =< succ y) : x =< y :=
match H with
  | LEsucc _ _ p => p
end.

Lemma Less_succ_inv : forall (x y : Nat), succ x <' succ y -> x <' y.
Proof.
intros x y H.
apply (LEsucc_inv (succ x) y H).
Qed.

Definition not_succ_LE_zero (x : Nat) (p : succ x =< 0) : Empty :=
match p with
end.

(*
Transitivity of LessOrEqual relation. This definition is quite covluted. The main techniuque use here is "dependent pattern matching". See explainations here
https://stackoverflow.com/questions/12544469/impossible-pattern-in-writing-implicit-proof-object-in-coq
*)

Fixpoint LE_trans (x y z : Nat) (xy : x =< y) (yz : y =< z) : x =< z :=
match x as x' return (forall (y z : Nat), (x' =< y) -> (y =< z) -> x' =< z) with
  | zero => fun y1 z1 xy1 yz1 => LEzero z1
  | succ x' => fun y1 z1 xy1 yz1 => 
    match y1 as y2 return (forall (z : Nat), succ x' =< y2 -> y2 =< z -> succ x' =< z) with
    | zero => fun z2 xy2 yz2 => Empty_rect (fun x => _) (not_succ_LE_zero _ xy2)
    | succ y' => fun z2 xy2 yz2 => match z2 as z3 return (succ x' =< succ y' -> succ y' =< z3 -> succ x' =< z3) with
      | zero => fun xy3 yz3 => Empty_rect (fun x => _) (not_succ_LE_zero _ yz3)
      | succ z' => (fun xy3 yz3 => LEsucc x' z' (LE_trans x' y' z' (LEsucc_inv x' y' xy3) (LEsucc_inv y' z' yz3)) )
      end xy2 yz2
    end z1 xy1 yz1
  end y z xy yz.


Lemma less_implies_le : forall (a b : Nat), a <' b -> a =< b.
Proof.
intros a b H.
apply (LE_trans a (succ a) b (x_le_xplus1 a) H).
Qed.

(* 
Side: how to define negation in Coq. 

Recall in boolean logic, given a boolean variable b, (b => false) = true iff b = false, and (b => false) = false iff b = true. In other word, not b = b => false.

If A is a Set, then (A -> Empty) is the set of functions from A to Empty. A -> Empty is empty iff A is not Empty, and A -> Empty is not empty iff A is Empty. We will define Not A to be A -> Empty. 

The idea behind this is what is called the "Brouwer-Heyting-Kolmogorov intepretation" or "BHK interpretation" of intuitionistic logic, or "Curry-Howard correspondence". Roughly speaking, we can regard a set or a type as a proposition and elments as proofs. E.g., a == a is a type and a proposition that a is equal to a, and refl is an element of a == a, and also a proof.

Back to the negation of a set A. If A is empty, or has no proof, then Not A should have a proof, i.e., there is one function in A -> Empty. On the other hand, if A has a proof, then Not A shouldn't have any proof, i.e. A -> Empty is empty.

To code the above, we have,
*)

Definition Not (A : Set) : Set := A -> Empty.

Definition Less_irrefl_0 : Not ( 0 <' 0)
  := fun p => not_succ_LE_zero 0 p.

Lemma Less_irrefl : forall (x : Nat), Not (x <' x).
Proof.
intros x H.
induction x.
  - exact (Less_irrefl_0 H).
  - exact (IHx (Less_succ_inv x x H)).
Qed.

(*
This is also quite convoluted. Also using "dependent pattern matching" technique. 
*)
Fixpoint LE_antisym (x y : Nat) (xy : x =< y) (yx : y =< x) : x == y :=
match x as x1 return (forall (y : Nat), x1 =< y -> y =< x1 -> x1 == y) with
  | zero => fun y xy yx => match y as y1 return (zero =< y1 -> y1 =< zero -> zero == y1) with
    | zero => fun _ _ => refl zero
    | succ y1' => fun xy yx => Empty_rect (fun x => _) (not_succ_LE_zero y1' yx)
    end xy yx 
  | succ x1'=> fun y xy yx => match y as y1 return (succ x1' =< y1 -> y1 =< succ x1' -> succ x1' == y1) with
    | zero => fun xy yx => Empty_rect (fun x => _) (not_succ_LE_zero x1' xy)
    | succ y1' => fun xy yx => Equal_context_succ x1' y1' (LE_antisym x1' y1' (LEsucc_inv _ _ xy) (LEsucc_inv _ _ yx))
    end xy yx
end y xy yx.

(*
With BHK interpretion in mind, we can definte logic "or" of two proposition.
*)
Inductive OR (A B : Set) : Set :=
  | or_introl : A -> OR A B
  | or_intror : B -> OR A B.

Notation "A \_/ B" := (OR A B) (at level 85, right associativity).

Check or_introl.
(* Check or_introl show the type of or_introl "forall A B : Set, A -> A \_/ B". If calling or_introl "or_introl A B a", A can be infered from a. If from context, B is also inferable, we use the following command to tell Coq, we will omit type arguments A and B as often as possible. *)
Arguments or_introl [A B] _, [A] B _.
Arguments or_intror [A B] _, A [B] _.

(* Given two natural numbers, we can decide which is larger. *)
Fixpoint decide_order (a : Nat) (b : Nat) : (a =< b) \_/ (b <' a) :=
  match a with
   | zero => or_introl (LEzero b)
   | succ a' => 
      match b with
        | zero => or_intror (zero_less_succ a')
        | succ b' => 
          match decide_order a' b' with
            | or_introl p => or_introl (LEsucc _ _ p)
            | or_intror p => or_intror (LEsucc _ _ p)
           end
      end
  end.

(* Have defined order on Nat and all kinds of properties of order. We are ready to define insertion sort. *)

Fixpoint insert (x : Nat) (l : ListNat) : ListNat :=
  match l with 
    | nil => con x nil
    | con h t => 
      match decide_order x h with
        | or_introl p => con x (con h t)
        | or_intror p => con h (insert x t)
      end
  end.

Compute (insert 5 (1 ; 2 ; 3 ; 6 ; 7 ; 9 ; nil)).

Fixpoint sort l :=
  match l with
    | nil => nil
    | h ; t => insert h (sort t)
  end.

Compute (sort (5;6;3;2;nil)).

(* Property of a list being sorted.*)
Inductive sorted : ListNat -> Set :=
  | sort_nil : sorted nil
  | sort_one : forall x, sorted (x ; nil)
  | sort_more : forall x y l,
                x =< y
                -> sorted (y ; l)
                -> sorted (x ; y ; l).

Example eg1 : sorted (1;2;3;nil).
Proof. 
exact (
  sort_more 1 2 (3 ; nil) (LEsucc 0 1 (LEzero 1)) 
    (sort_more 2 3 nil (LEsucc 1 2 (LEsucc 0 1 (LEzero 1)))
      (sort_one 3))). 
Qed.

Print eg1.

(* A non-empty list is sorted implies the tail is sorted. *)
Definition sorted_tail (h : Nat) (t : ListNat) (H : sorted (h ; t)) : sorted t :=
match H with 
(*  | sort_nil => sort_nil *)
  | sort_one x' => sort_nil
  | sort_more a b l' ab bl' => bl'
end.

(* We also want the sorted list to be a permutation of the orginial list, or equivalently, we want two lists have the same elements (counting duplicates).*)
Fixpoint count_occ (l : ListNat) (x : Nat) : Nat :=
  match l with
    | nil => 0
    | y ; tl =>
      let n := count_occ tl x in
        if equalNB y x then succ n else n
  end.

Compute (count_occ (3;2;4;5;2;2;nil) 2).

Definition permut (l1 l2 : ListNat) :=
   forall x:Nat, count_occ l1 x == count_occ l2 x.

(* Similar to OR connective, we can define logic AND. *)
Inductive AND (P Q : Set) : Set :=
  | conj : P -> Q -> AND P Q.

Notation "A /'\ B" := (AND A B)(at level 85, right associativity).
Arguments conj [P Q] _ _, P Q _ _.

(* Some properties of permutation. *)
Lemma permut_refl : forall l, permut l l.
Proof.
intro l.
unfold permut.
intro x.
exact (refl (count_occ l x)).
Qed.

Lemma permut_swap :
  forall x y l l',
    permut l l'
    -> permut (x ; y ; l) (y ; x ; l').
Proof.
  intros x y l l' H z. simpl.
  case (equalNB x z).
    - case (equalNB y z).
      + rewrite (H z). exact (refl (succ (succ (count_occ l' z)))).
      + rewrite (H z). exact (refl (succ (count_occ l' z))).
    -  case (equalNB y z).
      + rewrite (H z). exact (refl (succ (count_occ l' z))).
      + exact (H z).
Qed.

Lemma permut_trans:
  forall l l' l'',
    permut l l'
    -> permut l' l''
    -> permut l l''.
Proof.
  unfold permut.
  intros l l' l'' H1 H2 x.
  rewrite H1. apply H2.
Qed.

Lemma permut_cons:
  forall x l l',
    permut l l' -> permut (x ; l) (x ; l').
Proof.
  intros x l l' H z. simpl.
  case (equalNB x z).
    - rewrite (H z). exact (refl (succ (count_occ l' z))).
    - exact (H z).
Qed.

(* insert function respects order. *)
Theorem insert_correct :
  forall l x,
    sorted l -> sorted (insert x l).

Proof.
  intros l x H. elim H; simpl...
    - exact (sort_one x).
    - intro. case (decide_order x x0).
      + intro. exact (sort_more x x0 nil l0 (sort_one x0)).
      + intro. exact (sort_more x0 x nil (less_implies_le _ _ l0) (sort_one x)).
    - intros x0 y l0 xy yl. case (decide_order x y).
      + intros. case (decide_order x x0).
        * intros. exact (sort_more x x0 (y;l0) l2 (sort_more  x0 y l0 xy yl)).
        * intros. exact (sort_more x0 x (y;l0) (less_implies_le _ _ l2) (sort_more  x y l0 l1 yl)).
      + intros. case (decide_order x x0).
        * intros. exact (sort_more x x0 (y;l0) l2 (sort_more x0 y l0 xy yl)).
        * intros. simpl. exact (sort_more x0 y (insert x l0) xy H0).
Qed.


(* insert function respects permutation. *)
Theorem insert_permut :
  forall l x,
    permut (x ; l) (insert x l).

Proof.
intros l x.
induction l as [| h t IH].
  - simpl. apply permut_refl.
  - simpl. case (decide_order x h) as [ll | rr].
    + apply permut_refl.
    + apply (permut_trans (x;h;t) (h;x;t) (h;insert x t) (permut_swap x h t t (permut_refl t) ) (permut_cons h (x;t) (insert x t) IH)).
Qed.

Lemma sort_sorts : forall l, sorted (sort l).

Proof.
  induction l.
  - exact (sort_nil). 
  - simpl. apply insert_correct; auto.
Qed.

Lemma sort_permutes : forall l, permut l (sort l).
Proof.
 induction l; simpl.
 - intro x. unfold permut. simpl. exact (refl 0).
 - exact (permut_trans (n;l) (n;sort l) (insert n (sort l)) (permut_cons n l (sort l) IHl) (insert_permut (sort l) n)).
Qed. 

(* Insertion sort is correct. *)
Theorem sort_correctness :
  forall l, sorted (sort l) /'\ permut l (sort l).
Proof.
  split. apply sort_sorts. apply sort_permutes.
Qed.
