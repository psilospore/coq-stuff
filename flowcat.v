Require Import Arith.


Inductive value : Type :=
  | Nat (n : nat)
  | Bool (b : bool).

(* I could use a string here but this is fine. *)
Inductive variable : Type :=
  | X
  | Y
  | Z.

(* Using nats as levels *)
Inductive SLevel : Type := Level (n : nat).

(* TODO How can I infix this stuff?*)

Inductive expr: Type :=
  | ReadVar (v : variable)
  | Value (v : value)
  | Not (e : expr)
  | And (e1 : expr) (e2 : expr)
  | Or (e1 : expr) (e2 : expr)
  | Plus (e1 : expr) (e2 : expr)
  | Mult (e1 : expr) (e2 : expr)
  | Mod (e1 : expr) (e2: expr)
  | Compare (e1 : expr) (e2 : expr)
  | IfThenElse (e1 : expr) (e2 : expr) (e3 : expr).


(*
TODO
Don't know coq well enough to generalize this stuff for mlscat and flowcat.
to generalize for mlscat for instance I need a union type that fails
expressiosn for read control checks (getting FlowExprSuccessthing from memory)
and programs (reductions) that can fail write control checks (assignments)
*)
Inductive prog : Type :=
  | Done
  | TypeError (* minicat allows negative true as an expression *)
  | Assign (v: variable) (e : expr) (p : prog).

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
  end.

Inductive flowcatExprResult :=
  | FlowUndefined (* Variable is not defined*)
  | FlowTypeError (* negative boolean or non sense*)
  | FlowReadControlCheckFail
  | FlowExprSuccess (v: value).

Definition flowexprres_sequence_map (f : value -> value) (fe : flowcatExprResult) : flowcatExprResult :=
  match fe with
  | FlowExprSuccess v => FlowExprSuccess (f v)
  | _ => fe
  end.

Fixpoint flowcatEval (m : memory) (e : expr) : flowcatExprResult :=
  match e with
    | ReadVar v => 
      match (m v) with
        | Some v' => FlowExprSuccess v'
        | None => FlowUndefined
      end
    | Value v => FlowExprSuccess v
    | Not e' => match eval m e' with
        | FlowExprSuccess (Bool b) => Some (Bool (negb b))
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
  end.



