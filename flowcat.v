Require Import Arith.


Inductive value : Type :=
  | Nat (n : nat)
  | Bool (b : bool).

(* I could use a string here but this is fine. *)
Inductive variable : Type :=
  | X
  | Y
  | Z
  | H
  | L
  .

(* Using nats as levels *)
Inductive SLevel : Type := Level (n : nat).

(* Example Binary Security Lattice *)
(* Definition HiLevel  = Level 1.
Definition LowLevel = SLevel 0. *)

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
TODO handle unassigned memories
*)

Inductive Assignment : Type := Assignment (variable: variable) (expr : expr).

Inductive prog : Type :=
  | Naught
  | Step Assignment((v: variable) (e : expr)) (p : prog).

(* x = 4; y = 2;*)
Definition example_program := Step (Assignment X (Nat 4)) (Step Assighment Y (Nat 2) Naught)

Inductive RuntimeState : Type := RuntimeState (memory: Memory) (program : prog).
RuntimeState -> RuntimeState

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

Fixpoint reduce (s : RuntimeState) : RuntimeState :=
  update m (eval m a.expression)

Fixpoint reduce_multi (s : RuntimeState) : RuntimeState := TODO.

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

(* Example of eval running on a memory and an expression *)

Definition example_expr : expr := Value(Nat(1)).
Print example_expr.
Definition example_memory : partial_map value := empty.
Print example_memory.
Definition example_output := eval example_memory example_expr.
Print example_output.

(* End of example*)

(* TODO finish minicat *)

Inductive flowcatExprResult :=
  | FlowUndefined (* Variable is not defined*)
  | FlowTypeError (* negative boolean or non sense*)
  | FlowExprSuccess (v: value) (s : SLevel).


(*
Sequence then map
If success then run map function
Otherwise return first failure.
*)
Definition flow_seq_map (fe1 : flowcatExprResult) (fe2 : flowcatExprResult) (f : value -> value -> value): flowcatExprResult :=
  match (fe1, fe2) with
  | (FlowExprSuccess v1, FlowExprSuccess v2) => FlowExprSuccess (f v1 v2)
  | _ => fe1
  end.

Fixpoint flow_eval (m : memory) (e : expr) : flowcatExprResult :=
  match e with
    | ReadVar v => 
      match (m v) with
        | Some v' => FlowExprSuccess v'
        | None => FlowUndefined
      end
    | Value v => FlowExprSuccess v
    | Not e' => match flow_eval m e' with
        | FlowExprSuccess (Bool b) => FlowExprSuccess (Bool (negb b))
        | _ => FlowUndefined (* TODO return wildcard*)
      end
    | And e1 e2 => 
      flow_seq_map (flow_eval m e1) (flow_eval m e2) (fun b1 b2 => Some (Bool (andb b1 b2)))
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



(*

1. We could write out flowcat correctly.
2. We could pick some theorems we want to prove

1a. Write mlscat maybe it's easier
2a. Write some proofs.
*)