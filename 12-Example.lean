open Classical

def Env := String → Nat

def Env.insert (v : String) (n : Nat) (env : Env) : Env :=
  fun x => if x = v then n else env x

inductive Stmt where
  | skip : Stmt
  | assign : String → (Env → Nat) → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : (Env → Bool) → Stmt → Stmt → Stmt

noncomputable def evalStmt : Stmt → Env → Env
  | .skip, env => env
  | .assign v e, env => env.insert v (e env)
  | .seq S1 S2, env => evalStmt S2 (evalStmt S1 env)
  | .ifThenElse b S1 S2, env => if b env then evalStmt S1 env else evalStmt S2 env
