exception Error
exception Not_found

type exp = Var of string
| Lambda of exp*exp
| Call of exp*exp
| Unit
| T
| F
| Const of int
| Add of exp*exp
| Mul of exp*exp
| Equal of exp*exp
| Grt of exp*exp
| Lst of exp*exp
| Gre of exp*exp
| Lte of exp*exp
| Tup of (exp list)
| Proj of int*(exp)
| IfThenElse of exp*exp*exp
| Let of exp*exp 					(* first exp can be Def/SeqDefs/ParallelDefs/LocalFirstInSecondDef *)
| Def of exp*exp 					(* first exp to be Var *)
| SeqDefs of exp*exp 				(* both exps to be defs *)
| ParallelDefs of exp*exp 			(* both exps to be defs *)

let rec lookup t x = match t with
| [] -> raise Not_found
| (a,b) :: c -> if (a = x) then b else lookup c x

(* Krivine machine *)
type answerK = UnitK
| BoolTK
| BoolFK
| IntK of int
| AListK of answerK list
| TableExtensionK of (exp * exp) list
| VClosureK of ((exp * exp) list) * exp

let rec eval_call_by_name e = match e with
| (t,Var a) -> eval_call_by_name (t,(lookup t (Var a)))
| (t,Lambda (a,b)) -> VClosureK (t,Lambda (a,b))
| (t, Call(a,b)) -> (match (eval_call_by_name (t,a)) with
	| VClosureK (t1,Lambda (Var x,e1)) -> eval_call_by_name ((Var x,b)::t1,e1)
	| _ -> raise Error
	)
| (_,Unit) -> UnitK
| (_,T) -> BoolTK
| (_,F) -> BoolFK
| (_,Const a) -> IntK a
| (t,Add (a,b)) -> (match (eval_call_by_name (t,a), eval_call_by_name (t,b)) with
	| (IntK a1, IntK a2) -> IntK (a1+a2)
	| (_,_) -> raise Error
	)
| (t,Mul (a,b)) -> (match (eval_call_by_name (t,a), eval_call_by_name (t,b)) with
	| (IntK a1, IntK a2) -> IntK (a1*a2)
	| (_,_) -> raise Error
	)
| (t,Equal (a,b)) -> (match (eval_call_by_name (t,a), eval_call_by_name (t,b)) with
	| (IntK a1, IntK a2) -> if a1=a2 then BoolTK else BoolFK
	| (_,_) -> raise Error
	)
| (t,Grt (a,b)) -> (match (eval_call_by_name (t,a), eval_call_by_name (t,b)) with
	| (IntK a1, IntK a2) -> if a1>a2 then BoolTK else BoolFK
	| (_,_) -> raise Error
	)
| (t,Lst (a,b)) -> (match (eval_call_by_name (t,a), eval_call_by_name (t,b)) with
	| (IntK a1, IntK a2) -> if a1<a2 then BoolTK else BoolFK
	| (_,_) -> raise Error
	)
| (t,Gre (a,b)) -> (match (eval_call_by_name (t,a), eval_call_by_name (t,b)) with
	| (IntK a1, IntK a2) -> if a1>=a2 then BoolTK else BoolFK
	| (_,_) -> raise Error
	)
| (t,Lte (a,b)) -> (match (eval_call_by_name (t,a), eval_call_by_name (t,b)) with
	| (IntK a1, IntK a2) -> if a1<=a2 then BoolTK else BoolFK
	| (_,_) -> raise Error
	)
| (t,Tup a) -> AListK (List.map (eval_call_by_name) (List.map ((fun x -> (t,x))) a))
| (t,Proj (a,Tup b)) -> eval_call_by_name (t,(List.nth b a))
| (t,IfThenElse (a,b,c)) -> (match (eval_call_by_name (t,a)) with
	| BoolTK -> eval_call_by_name (t,b)
	| BoolFK -> eval_call_by_name (t,c)
	| _ -> raise Error
	)
| (t, Let (e1,e2)) -> (match (eval_call_by_name (t,e1)) with
	| TableExtensionK t1 -> eval_call_by_name ((t1@t), e2)
	| _ -> raise Error
	)
| (t,Def (Var x,e2)) -> TableExtensionK [(Var x, e2)]
| (t,SeqDefs (e1,e2)) -> (match (eval_call_by_name (t,e1)) with
	| TableExtensionK t1 -> (match (eval_call_by_name ((t1@t),e2)) with
		| TableExtensionK t2 -> TableExtensionK (t1@t2)
		| _ -> raise Error
		)
	| _ -> raise Error
	)
| (t,ParallelDefs (e1,e2)) -> (match (eval_call_by_name (t,e1), eval_call_by_name (t,e2)) with
	| (TableExtensionK t1, TableExtensionK t2) -> TableExtensionK (t1@t2)
	| (_,_) -> raise Error
	)
| _ -> raise Error

(* 
eg : let a = Call (Lambda (Add (Var "x",Const 1)), Const 2);;
	 eval_call_by_name ([],a);;
	 - : answerK = IntK 3
 *)

(* SECD machine *)
type opcode = 
| Ovar of string
| Oclosure of exp*(opcode list)
| Oret
| Oapply
| Ounit
| Otrue
| Ofalse
| Oint of int
| Oadd
| Omul
| Oequal
| Ogrt
| Olst
| Ogre
| Olte
| Otup
| OtupBeg
| Oproj
| OIfThenElse
| Obind
| Ounbind
| Odef of exp
| OseqDefs
| OseqDefsEnd
| OParallelDefs

type answer = UnitA
| BoolT
| BoolF
| Int of int
| AList of answer list
| TableExtension of (exp * answer) list
| VClosure of ((exp * answer) list) * exp
| Closure of exp * ((exp * answer) list) * (opcode list)

let rec eval_call_by_value t e = match e with
| Var a -> lookup t e
| Lambda (a,b) -> VClosure (t,Lambda (a,b))
| Call (a,b) -> (match (eval_call_by_value t a) with
	| VClosure (t1,Lambda (Var x, e1)) -> eval_call_by_value ((Var x, eval_call_by_value t b)::t1) e1
	| _ -> raise Error
	)
| Unit -> UnitA
| T -> BoolT
| F -> BoolF
| Const a -> Int a
| Add (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (Int a1, Int a2) -> Int (a1+a2)
	| (_,_) -> raise Error
	)
| Mul (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (Int a1, Int a2) -> Int (a1*a2)
	| (_,_) -> raise Error
	)
| Equal (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (Int a1, Int a2) -> if (a1 = a2) then BoolT else BoolF
	| (_,_) -> raise Error
	)
| Grt (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (Int a1, Int a2) -> if (a1 > a2) then BoolT else BoolF
	| (_,_) -> raise Error
	)
| Lst (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (Int a1, Int a2) -> if (a1 < a2) then BoolT else BoolF
	| (_,_) -> raise Error
	)
| Gre (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (Int a1, Int a2) -> if (a1 >= a2) then BoolT else BoolF
	| (_,_) -> raise Error
	)
| Lte (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (Int a1, Int a2) -> if (a1 <= a2) then BoolT else BoolF
	| (_,_) -> raise Error
	)
| Tup a -> AList (List.map (eval_call_by_value t) a)
| Proj (a,Tup b) -> eval_call_by_value t (List.nth b a)
| IfThenElse (e1,e2,e3) -> (match (eval_call_by_value t e1, eval_call_by_value t e2, eval_call_by_value t e3) with
	| (BoolT,a1,a2) -> a1
	| (BoolF,a1,a2) -> a2
	| (_,_,_) -> raise Error
	)
| Let (e1,e2) -> (match (eval_call_by_value t e1) with
	| TableExtension t1 -> eval_call_by_value (t1@t) e2
	| _ -> raise Error
	)
| Def (Var x,e2) -> TableExtension [(Var x, (eval_call_by_value t e2))]
| SeqDefs (e1,e2) -> (match (eval_call_by_value t e1) with
	| TableExtension t1 -> (match (eval_call_by_value (t1@t) e2) with
		| TableExtension t2 -> TableExtension (t1@t2)
		| _ -> raise Error
		)
	| _ -> raise Error
	)
| ParallelDefs (e1,e2) -> (match (eval_call_by_value t e1, eval_call_by_value t e2) with
	| (TableExtension t1, TableExtension t2) -> TableExtension (t1@t2)
	| (_,_) -> raise Error
	)
| _ -> raise Error

let rec compile e = match e with
| Var a -> [Ovar a]
| Lambda (a,b) -> [Oclosure (a,((compile b)@[Oret]))]
| Call (a,b) -> (compile a)@(compile b)@[Oapply]
| Unit -> [Ounit]
| T -> [Otrue]
| F -> [Ofalse]
| Const a -> [Oint a]
| Add (e1,e2) -> (compile e2)@(compile e1)@[Oadd]
| Mul (e1,e2) -> (compile e2)@(compile e1)@[Omul]
| Equal (e1,e2) -> (compile e1)@(compile e2)@[Oequal]
| Grt (e1,e2) ->  (compile e1)@(compile e2)@[Ogrt]
| Lst (e1,e2) ->  (compile e1)@(compile e2)@[Olst]
| Gre (e1,e2) ->  (compile e1)@(compile e2)@[Ogre]
| Lte (e1,e2) ->  (compile e1)@(compile e2)@[Olte]
| Tup a ->  (match (a) with
    | x::[] -> (compile x)@[OtupBeg]
    | x::xs -> (compile (Tup xs))@(compile x)@[Otup]
	| _ -> raise Error )
| Proj (a,Tup b) -> [Oint a]@(compile (Tup b))@[Oproj]
| IfThenElse (e1,e2,e3) -> (compile e1)@(compile e2)@compile(e3)@[OIfThenElse]
| Let (e1,e2) -> (compile e1)@[Obind]@(compile e2)@[Ounbind]
| Def (Var x, e2) -> (compile e2)@[Odef (Var x)]
| SeqDefs (e1,e2) -> (compile e1)@[OseqDefs]@(compile e2)@[OseqDefsEnd]
| ParallelDefs (e1,e2) -> (compile e1)@(compile e2)@[OParallelDefs]
| _ -> raise Error

let rec execute s t c d = match (s,c) with
| (s0::s1, []) -> s0
| (_,(Ovar b)::c1) -> execute ((lookup t (Var b))::s) t c1 d
| (_,(Oclosure (a,b))::c1) -> execute ((Closure(a, t, b))::s) t c1 d
| (s0::(Closure(x0, t0,c0))::s1,(Oapply)::c1) -> execute [] ((x0,s0)::t0) c0 ((s1,t,c1)::d)
| (s0::s2,(Oret)::c1) -> (match d with
	| (s1,t1,c1)::d1 -> execute (s0::s1) t1 c1 d1
	| _ -> raise Error
	)
| (_,(Ounit)::c1) -> execute (UnitA::s) t c1 d
| (_,(Otrue)::c1) -> execute (BoolT::s) t c1 d
| (_,(Ofalse)::c1) -> execute (BoolF::s) t c1 d
| (_, (Oint b)::c1) -> execute ((Int b)::s) t c1 d
| ((Int a0)::(Int a1)::s2, (Oadd)::c1) -> execute ((Int (a0+a1))::s2) t c1 d
| ((Int a0)::(Int a1)::s2, (Omul)::c1) -> execute ((Int (a0*a1))::s2) t c1 d
| ((Int a0)::(Int a1)::s2, (Oequal)::c1) -> if (a0 = a1) then execute (BoolT::s2) t c1 d else execute (BoolF::s2) t c1 d
| ((Int a0)::(Int a1)::s2, (Ogrt)::c1) -> if (a1>a0) then execute (BoolT::s2) t c1 d else execute (BoolF::s2) t c1 d
| ((Int a0)::(Int a1)::s2, (Olst)::c1) -> if (a1<a0) then execute (BoolT::s2) t c1 d else execute (BoolF::s2) t c1 d
| ((Int a0)::(Int a1)::s2, (Ogre)::c1) -> if (a1>=a0) then execute (BoolT::s2) t c1 d else execute (BoolF::s2) t c1 d
| ((Int a0)::(Int a1)::s2, (Olte)::c1) -> if (a1<=a0) then execute (BoolT::s2) t c1 d else execute (BoolF::s2) t c1 d
| (a::(AList b)::s1, Otup::c1) -> execute ((AList (a::b))::s1) t c1 d
| (a::s1, OtupBeg::c1) -> execute ((AList [a])::s1) t c1 d
| ((AList b)::(Int a)::s1,Oproj::c1) -> execute ((List.nth b a)::s1) t c1 d
| (a0::a1::BoolT::s1, (OIfThenElse)::c1) -> execute (a1::s1) t c1 d
| (a0::a1::BoolF::s1, (OIfThenElse)::c1) -> execute (a0::s1) t c1 d
| ((TableExtension t1)::s1, (Obind)::c1) -> execute s1 (t1@t) c1 ((s1,t,c1)::d)
| (_,(Ounbind)::c1) -> (match d with
	| (s1,t1,c2)::d1 -> execute s t1 c1 d1
	| _ -> raise Error
	)
| ((TableExtension t1)::s1, (OseqDefs)::c1) -> execute s (t1@t) c1 ((s,t,c1)::d)
| ((TableExtension t2)::(TableExtension t1)::s1, (OseqDefsEnd)::c1) -> (match d with
	| (s2,t3,c2)::d1 -> execute ((TableExtension (t1@t2))::s) t3 c1 d1
	| _ -> raise Error
	)
| (a0::s1, (Odef (Var x))::c1) -> execute ((TableExtension [(Var x,a0)])::s1) t c1 d
| ((TableExtension t1)::(TableExtension t2)::s1, (OParallelDefs)::c1) -> execute ((TableExtension (t1@t2))::s1) t c1 d
| (_,_) -> raise Error

(* 
eg : let a = Call (Lambda (Var "x", Add (Var "x",Const 1)), Const 2);;
	 eval_call_by_value [] a;;
	 - : answer = Int 3

	 let b = compile a;;
	 val b : opcode list =
  	 [Oclosure [Oint 1; Ovar "x"; Oadd; Oret]; Oint 2; Oapply]
	 execute [] [] b [];;
	 - : answer = Int 3
 *);;