

(* Inductive bool : Type :=
  | true
  | false.

Inductive nat : Type :=
  | O
  | S (n : nat).
 *)

Inductive value : Type :=
  | Nat (n : nat)
  | Bool (b : bool).

(* Not sure how to make any unique symbol a variable. *)
Inductive variable : Type :=
  | X
  | Y.

(* Using nats as levels *)
Inductive SLevel : Type := Level (n : nat).


(* How can I infix this*)

Inductive expr: Type :=
  | ReadVar (v : variable)
  | Value (v : value)
  | Negative (e : expr)
  | Not (e : expr)
  | And (e : expr) (e : expr)
  | Or (e : expr) (e : expr)
  | Plus (e : expr) (e : expr)
  | Mult (e : expr) (e : expr)
  | Mod (e : expr) (e: expr)
  | Compare (e : expr) (e : expr)
  | IfThenElse (e : expr) (e : expr) (e : expr).

Notation "-expr" := (Negative (Value (Nat expr)))
                       (at level 50, left associativity).

Notation "x + y" := (Plus (Value (Nat x)) (Value (Nat y)))
                       (at level 50, left associativity).

Notation "x * y" := (Mult (Value (Nat x)) (Value (Nat y)))
                       (at level 40, left associativity).

Notation "x % y" := (Mod (Value (Nat x)) (Value (Nat y)))
                       (at level 40, left associativity).

Notation "x == y" := (Compare (Value (Nat x)) (Value (Nat y)))
                       (at level 40, left associativity).

Check (0 + 1 * 4) : expr.

Inductive prog: Type :=
  | Done
  | Assign (v: variable) (e : expr) (p : prog).

(* Notation "X = E; P" := (Assign X E P) (at level 200).
 Doesn't work idk why*)

(* 
Now we need memory. We can use a Map.
Creating a Map idk how to use the stdlib https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html
*)
Definition total_map (A : Type) := variable -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition var_eqb (x: variable) (x' : variable) : bool :=
  match (x, x') with
    | (X, X) => true
    | (Y, Y) => true
    | _ => false
  end.

Definition t_update {A : Type} (m : total_map A)
                    (x : variable) (v : A) :=
  fun x' => if var_eqb x x' then v else m x'.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).


Definition update {A : Type} (m : partial_map A)
           (x : variable) (v : A) :=
  (x !-> Some v ; m).

Definition memory := partial_map variable.

Fixpoint minicat_eval (m : memory) (p: prog) : prog :=
  match p with
    | Done => Done
    | Assign (v) (e) (p) => Done
  end. 








