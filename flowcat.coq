Require Import Arith.

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
  | Not (e : expr)
  | And (e : expr) (e : expr)
  | Or (e : expr) (e : expr)
  | Plus (e : expr) (e : expr)
  | Mult (e : expr) (e : expr)
  | Mod (e : expr) (e: expr)
  | Compare (e : expr) (e : expr)
  | IfThenElse (e : expr) (e : expr) (e : expr).

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
  | BadExpression
  | Stuck
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

Notation "x '⊢>' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Definition memory := partial_map value.


Fixpoint eval (m : memory) (e : expr) : option value :=
  match e with
    | ReadVar v => m v
    | Value v => Some v
    | Not e' => 
      match eval m e' with
        | Some (Bool b) => Some (Bool (negb b))
        | _ => None
      end
    | And e1 e2 => 
      match eval m e1, eval m e2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (andb b1 b2))
        | _, _ => None
      end
    | Or e1 e2 => 
      match eval m e1, eval m e2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (orb b1 b2))
        | _, _ => None
      end
    | Plus e1 e2 => 
      match eval m e1, eval m e2 with
        | Some (Nat n1), Some (Nat n2) => Some (Nat (n1 + n2))
        | _, _ => None
      end
    | Mult e1 e2 => 
      match eval m e1, eval m e2 with
        | Some (Nat n1), Some (Nat n2) => Some (Nat (n1 * n2))
        | _, _ => None
      end
    | Mod e1 e2 => 
      match eval m e1, eval m e2 with
        | Some (Nat n1), Some (Nat n2) => Some (Nat (n1 mod n2))
        | _, _ => None
      end
    | Compare e1 e2 => 
      match eval m e1, eval m e2 with
        | Some (Nat n1), Some (Nat n2) => Some (Bool (beq_nat n1 n2))
        | _, _ => None
      end
    | IfThenElse e1 e2 e3 => 
      match eval m e1 with
        | Some (Bool b) => 
          if b then eval m e2 else eval m e3
        | _ => None
      end
  end.H


Fixpoint minicat_exec (m : memory) (p : prog) : (memory, prog) :=
  match p with
    | Done => (m, Done)
    | Stuck => (m, Stuck)
    | TypeError => (m, TypeError)
    | Assign v e p => 
      match eval m e with
        | Some v' => minicat_exec (update m v v') p
        | None => (m, T)
      end
  end.

Fixpoint minicat_eval (m : memory) (p: prog) : prog :=
  match p with
    | Done => Done
    | Stuck => Stuck
    | Assign (v) (e) (p) => match e with 
      | ReadVar (v) => Done
      | Value (v) => Stuck
      | Negative (e ) => Stuck
      | Not (e) => Stuck
      | And (e) (e : expr) => Stuck
      | Or (e) (e) => Stuck
      | Plus (e) (e) => Stuck
      | Mult (e) (e) => Stuck
      | Mod (e) (e) => Stuck
      | Compare (e) (e) => Stuck
      | IfThenElse (e) (e) (e) => Stuck
    end.
  end. 


Fixpoint minicat_eval (m : memory) (p: prog) : prog :=
  match p with
    | Done => Done
    | Stuck => Stuck
    | Assign v e p => 
      let m' := update_memory m v (eval_expr m e) in
      minicat_eval m' p
  end

with eval_expr (m : memory) (e: expr) : value :=
  match e with
    | ReadVar v => read_memory m v
    | Value v => v
    | Negative e => neg (eval_expr m e)
    | Not e => not (eval_expr m e)
    | And e1 e2 => and (eval_expr m e1) (eval_expr m e2)
    | Or e1 e2 => or (eval_expr m e1) (eval_expr m e2)
    | Plus e1 e2 => plus (eval_expr m e1) (eval_expr m e2)
    | Mult e1 e2 => mult (eval_expr m e1) (eval_expr m e2)
    | Mod e1 e2 => modulo (eval_expr m e1) (eval_expr m e2)
    | Compare e1 e2 => cmp (eval_expr m e1) (eval_expr m e2)
    | IfThenElse e1 e2 e3 => if_then_else (eval_expr m e1) (eval_expr m e2) (eval_expr m e3)
  end.



