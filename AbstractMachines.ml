exception Error
exception Error1
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
type closureK = ClosK of ((exp * closureK) list) * exp

type answerK = UnitK
| BoolTK
| BoolFK
| IntK of int
| AListK of answerK list
| TableExtensionK of (exp * closureK) list
| VClosureK of ((exp * closureK) list) * exp

let rec eval_call_by_name e = match e with
| (t,Var a) -> (match (lookup t (Var a)) with
	| ClosK(t1,b) -> eval_call_by_name (t1,b)
	)
| (t,Lambda (a,b)) -> VClosureK (t,Lambda (a,b))
| (t, Call(a,b)) -> (match (eval_call_by_name (t,a)) with
	| VClosureK (t1,Lambda (Var x,e1)) -> eval_call_by_name ((Var x , ClosK(t,b))::t1,e1)
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
| (t,Def (Var x,e2)) -> TableExtensionK [(Var x, ClosK (t,e2))]
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

type opcodeK = OClosK of ((exp * closureK) list) * exp

| OAddNextK of ((exp * closureK) list) * exp
| OAddCompleteK of ((exp * closureK) list) * exp

| OMulNextK of ((exp * closureK) list) * exp
| OMulCompleteK of ((exp * closureK) list) * exp

| OEqualNextK of ((exp * closureK) list) * exp
| OEqualCompleteK of ((exp * closureK) list) * exp

| OGrtNextK of ((exp * closureK) list) * exp
| OGrtCompleteK of ((exp * closureK) list) * exp

| OLstNextK of ((exp * closureK) list) * exp
| OLstCompleteK of ((exp * closureK) list) * exp

| OGreNextK of ((exp * closureK) list) * exp
| OGreCompleteK of ((exp * closureK) list) * exp

| OLteNextK of ((exp * closureK) list) * exp
| OLteCompleteK of ((exp * closureK) list) * exp

| OTupK of ((exp * closureK) list) * (exp list)
| OTupCompleteK of (exp list)
| OTupDoneK


| OIfThenElseK of ((exp * closureK) list) * exp * exp

| OTableExtensionK of (exp * closureK) list

| OSeqDefsK of ((exp * closureK) list) * exp

| OParallelDefsK of ((exp * closureK) list) * exp


let rec executeK clos s = match clos with
| ClosK (t,Var x) -> executeK  (lookup t (Var x)) s
| ClosK (t,Lambda (a,b)) -> (match s with
	| (OClosK(t1,e1))::xs -> executeK (ClosK((a,ClosK(t1,e1))::t,b)) xs
	| _ -> raise Error
	)
| ClosK (t,Call (a,b)) -> executeK (ClosK (t,a)) ((OClosK (t,b))::s)
| ClosK (t,Unit) -> (match s with
	| [] -> ClosK ([], Unit)
	| (OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [Unit])::s1)
	| (OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [Unit])::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[Unit]))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[Unit]))::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::s1 -> executeK (ClosK (t,Tup (l@[Unit]))) (OTupDoneK::s1)
	| _ -> raise Error
	)
| ClosK (t,T) -> (match s with
	| [] -> ClosK ([], T)
	| (OIfThenElseK (t1,e1,e2))::s1 -> executeK (ClosK (t1,e1)) s1
	| (OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [T])::s1)
	| (OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [T])::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[T]))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[T]))::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::s1 -> executeK (ClosK (t,Tup (l@[T]))) (OTupDoneK::s1)
	| _ -> raise Error
	)
| ClosK (t,F) -> (match s with
	| [] -> ClosK ([], F)
	| (OIfThenElseK (t1,e1,e2))::s1 -> executeK (ClosK (t1,e2)) s1
	| (OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [F])::s1)
	| (OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [F])::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[F]))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[F]))::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::s1 -> executeK (ClosK (t,Tup (l@[F]))) (OTupDoneK::s1)
	| _ -> raise Error
	)
| ClosK (t,Const a) -> (match s with
	| [] -> ClosK ([], Const a)

	| (OAddNextK (t1,e1))::s1 -> executeK (ClosK (t1,e1)) ((OAddCompleteK(t1,Const a))::s1)
	| (OAddCompleteK (t2,Const a2))::s2 -> executeK (ClosK (t2,Const (a+a2))) s2

	| (OMulNextK (t1,e1))::s1 -> executeK (ClosK (t1,e1)) ((OMulCompleteK(t1,Const a))::s1)
	| (OMulCompleteK (t2,Const a2))::s2 -> executeK (ClosK (t2,Const (a*a2))) s2
	
	| (OEqualNextK (t1,e1))::s1 -> executeK (ClosK (t1,e1)) ((OEqualCompleteK(t1,Const a))::s1)
	| (OEqualCompleteK (t2,Const a2))::s2 -> if (a = a2) then executeK (ClosK (t2,T)) s2 else executeK (ClosK (t2,F)) s2

	| (OGrtNextK (t1,e1))::s1 -> executeK (ClosK (t1,e1)) ((OGrtCompleteK(t1,Const a))::s1)
	| (OGrtCompleteK (t2,Const a2))::s2 -> if (a2 > a) then executeK (ClosK (t2,T)) s2 else executeK (ClosK (t2,F)) s2

	| (OLstNextK (t1,e1))::s1 -> executeK (ClosK (t1,e1)) ((OLstCompleteK(t1,Const a))::s1)
	| (OLstCompleteK (t2,Const a2))::s2 -> if (a2 < a) then executeK (ClosK (t2,T)) s2 else executeK (ClosK (t2,F)) s2

	| (OGreNextK (t1,e1))::s1 -> executeK (ClosK (t1,e1)) ((OGreCompleteK(t1,Const a))::s1)
	| (OGreCompleteK (t2,Const a2))::s2 -> if (a2 >= a) then executeK (ClosK (t2,T)) s2 else executeK (ClosK (t2,F)) s2

	| (OLteNextK (t1,e1))::s1 -> executeK (ClosK (t1,e1)) ((OLteCompleteK(t1,Const a))::s1)
	| (OLteCompleteK (t2,Const a2))::s2 -> if (a2 <= a) then executeK (ClosK (t2,T)) s2 else executeK (ClosK (t2,F)) s2

	| (OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [Const a])::s1)
	| (OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK [Const a])::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::[]))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[Const a]))::s1)
	| (OTupCompleteK l)::(OTupK (t1, x::xs))::s1 -> executeK (ClosK (t1,x)) ((OTupCompleteK (l@[Const a]))::(OTupK (t1, xs))::s1)
	| (OTupCompleteK l)::s1 -> executeK (ClosK (t,Tup (l@[Const a]))) (OTupDoneK::s1)
	
	| _ -> raise Error
	)
| ClosK (t,Add(a,b)) -> executeK (ClosK (t,a)) ((OAddNextK(t,b))::s)
| ClosK (t,Mul(a,b)) -> executeK (ClosK (t,a)) ((OMulNextK(t,b))::s)
| ClosK (t,Equal(a,b)) -> executeK (ClosK (t,a)) ((OEqualNextK(t,b))::s)
| ClosK (t,Grt(a,b)) -> executeK (ClosK (t,a)) ((OGrtNextK(t,b))::s)
| ClosK (t,Lst(a,b)) -> executeK (ClosK (t,a)) ((OLstNextK(t,b))::s)
| ClosK (t,Gre(a,b)) -> executeK (ClosK (t,a)) ((OGreNextK(t,b))::s)	
| ClosK (t,Lte(a,b)) -> executeK (ClosK (t,a)) ((OLteNextK(t,b))::s)
| ClosK (t,IfThenElse (a,b,c)) -> executeK (ClosK (t,a)) ((OIfThenElseK(t,b,c))::s)
| ClosK (t,Tup l) -> (match (l,s) with
	| (_, (OTupDoneK)::(OTupK (t1, x::[]))::s1) -> executeK (ClosK (t1,x)) ((OTupCompleteK [Tup l])::s1)
	| (_, (OTupDoneK)::(OTupK (t1, x::xs))::s1) -> executeK (ClosK (t1,x)) ((OTupCompleteK [Tup l])::(OTupK (t1, xs))::s1)
	| (_, (OTupDoneK)::(OTupCompleteK l1)::(OTupK (t1, x::[]))::s1) -> executeK (ClosK (t1,x)) ((OTupCompleteK (l1@[Tup l]))::s1)
	| (_, (OTupDoneK)::(OTupCompleteK l1)::(OTupK (t1, x::xs))::s1) -> executeK (ClosK (t1,x)) ((OTupCompleteK (l1@[Tup l]))::(OTupK (t1, xs))::s1)
	| (_, (OTupDoneK)::(OTupCompleteK l1)::[]) -> ClosK ([],Tup (l1@[Tup l]))
	| (_, (OTupDoneK)::[]) -> ClosK ([],Tup l)

	| ([],[]) -> clos
	| (x::[],s1) -> executeK (ClosK (t,x)) ((OTupCompleteK [])::s1)
	| (x::xs,s1) -> executeK (ClosK (t,x)) ((OTupK (t,xs))::s1) 
	
	| (_,_) -> raise Error1
	)
| ClosK (t,Let(a,b)) -> executeK (ClosK (t,a)) ((OClosK (t,b))::s)
| ClosK (t,Def (Var x, a)) -> (match s with
	| (OClosK (t1,b))::s1 -> executeK (ClosK ((Var x,ClosK(t,a))::t1,b)) s1
	| (OSeqDefsK (t1,d2))::(OTableExtensionK (t2))::s1 -> executeK (ClosK ((Var x,ClosK(t,a))::t1,d2)) ((OTableExtensionK ((Var x,ClosK(t,a))::t2))::s1)
	| (OSeqDefsK (t1,d2))::s1 -> executeK (ClosK ((Var x,ClosK(t,a))::t1,d2)) ((OTableExtensionK ([(Var x,ClosK(t,a))]))::s1)
	| (OParallelDefsK (t1,d2))::(OTableExtensionK (t2))::s1 -> executeK (ClosK (t1,d2)) ((OTableExtensionK ((Var x,ClosK(t,a))::t2))::s1) 
	| (OParallelDefsK (t1,d2))::s1 -> executeK (ClosK (t1,d2)) ((OTableExtensionK ([(Var x,ClosK(t,a))]))::s1)
	| (OTableExtensionK (t1))::(OClosK (t2,b))::s1 -> executeK (ClosK ((Var x,ClosK(t,a))::(t1@t2),b)) s1
	| _ -> raise Error
	)
| ClosK (t,SeqDefs (d1,d2)) -> executeK (ClosK (t,d1)) ((OSeqDefsK (t,d2))::s)
| ClosK (t,ParallelDefs (d1,d2)) -> executeK (ClosK (t,d1)) ((OParallelDefsK (t,d2))::s)
| _ -> raise Error


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
	| (s2,t3,c2)::d1 -> execute ((TableExtension (t1@t2))::s1) t3 c1 d1
	| _ -> raise Error
	)
| (a0::s1, (Odef (Var x))::c1) -> execute ((TableExtension [(Var x,a0)])::s1) t c1 d
| ((TableExtension t1)::(TableExtension t2)::s1, (OParallelDefs)::c1) -> execute ((TableExtension (t1@t2))::s1) t c1 d
| (_,_) -> raise Error

(* 
eg : let a = Call (Lambda (Var "x", Add (Var "x",Const 1)), Const 2);;
	 eval_call_by_value [] a;;
	 execute [] [] (compile a) [];;
	 eval_call_by_name ([],a);;
	 executeK (ClosK ([],a)) [];;

 *)

(*
	let a = Not (Grt (Const 6, Mod (Const 3, Const 2)));;
	let a = Tup [Const 1; Const 1; Add (Const 10, Const 5)];;
	let a = Tup [Const 1; Tup [Const 2; Const 3]; Add (Const 10, Const 5)];;

	let a = Let (Def (Var "x",Const 3), Call(Lambda (Var "y", Add (Var "y", Const 4)), Const 2));;
	let a = Let (Def (Var "x",Const 3), Call(Lambda (Var "y", Add (Var "y", Const 4)), Add(Var "x", Const 2)));;
	let a = Let (Def (Var "x",Const 3), Call(Lambda (Var "y", (Let (Def (Var "x",Const 10),Add (Var "y", Const 4)))), Add(Var "x", Const 2)));;

	let a = Let (ParallelDefs (Def (Var "y",Const 1), Def (Var "z",Const 2)), Add (Var "y",Var "z"))
	let a = Let (ParallelDefs (Def (Var "y",Const 2), SeqDefs (Def (Var "z",Const 2), Def (Var "w",Add(Var "z", Const 3)))), Mul (Var "y",Var "w"))
 *)
;;