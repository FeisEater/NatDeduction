    module NatDeduction where
    
    import Data.List
    
    data Atom = Prop String | Pred String [Variable] deriving (Eq)
    
    data Variable = Term String | Function String [Variable] deriving (Eq)
    
    data Formula = 	Atom Atom |
                    Not Formula |
                    Bin Binary Formula Formula |
                    Quan Quantifier Variable Formula --deriving (Show)
    data Binary = And | Or | If | Iff deriving (Eq, Show)
    data Quantifier = All | Exists deriving (Eq, Show)
    
    instance Eq Formula where
        Atom a == Atom b = a == b
        Not a == Not b = a == b
        Bin x a1 a2 == Bin y b1 b2 = ((a1 == b1 && a2 == b2) || (a1 == b2 && a2 == b1)) && x == y
        Quan p x a == Quan q y b = x == y && a == b && p == q
        --Not (Not a) == b = (a == b)
        --b == Not (Not a) = (a == b)
        _ == _ = False
        
    instance Show Formula where
        show (Atom a) = show a
        show (Not a) = '-' : show a
        show (Bin x a b) = '(' : show a ++ binChar x ++ show b ++ ")"
            where   binChar And = " & "
                    binChar Or = " | "
                    binChar If = " -> "
                    binChar Iff = " <-> "
        show (Quan q x a) = (qChar q) : show x ++ ":" ++ show a
            where   qChar All = '@'
                    qChar Exists = '#'

    instance Show Atom where
        show (Prop p) = p
        show (Pred p xs) = p ++ show xs
        
    instance Show Variable where
        show (Term t) = t
        show (Function f xs) = f ++ "{" ++ (sh xs) ++ "}"
            where   sh [] = ""
                    sh (x:[]) = show x
                    sh (x:xs) = show x ++ "," ++ sh xs
        
    readFormula :: String -> Formula
    readFormula ('-':xs) = Not (readFormula xs)
    readFormula ('@':xs) = let (term, rest) = break (== ':') xs in Quan All (readTerm term) (readFormula (tail rest))
    readFormula ('#':xs) = let (term, rest) = break (== ':') xs in Quan Exists (readTerm term) (readFormula (tail rest))
    readFormula ('(':xs) = findConnective 0 "" (init xs)
        where   findConnective 0 s (_:'&':_:xs) = Bin And (readFormula s) (readFormula xs)
                findConnective 0 s (_:'|':_:xs) = Bin Or (readFormula s) (readFormula xs)
                findConnective 0 s (_:'-':'>':_:xs) = Bin If (readFormula s) (readFormula xs)
                findConnective 0 s (_:'<':'-':'>':_:xs) = Bin Iff (readFormula s) (readFormula xs)
                findConnective n s ('(':xs) = findConnective (n+1) (s ++ "(") xs
                findConnective n s (')':xs) = findConnective (n-1) (s ++ ")") xs
                findConnective _ _ [] = Atom (Prop "Parse error")
                findConnective n s (x:xs) = findConnective n (s ++ [x]) xs
    readFormula xs
            | elem '[' xs = let (p, terms) = break (== '[') xs in Atom $ Pred p (readTerms (tail $ init $ terms))
            | otherwise = Atom (Prop xs)
        
    readTerm :: String -> Variable
    readTerm xs = head (readTerms xs)
    
    readTerms :: String -> [Variable]
    readTerms xs
        | null xs = []
        | elem '{' t = 
            let (f, other) = getFunction str (0-1) 
                (name, terms) = break (== '{') f
            in (Function name (readTerms (tail terms))):(readTerms other)
        | otherwise = (Term t):(readTerms ts)
        where   str = if head xs == ',' then tail xs else xs
                (t,ts) = break (== ',') str
                getFunction ('}':xs) 0 = ("",xs)
                getFunction ('{':xs) n = let f = getFunction xs (n+1) in ('{':(fst f), snd f)
                getFunction ('}':xs) n = let f = getFunction xs (n-1) in ('}':(fst f), snd f)
                getFunction (x:xs) n = let f = getFunction xs n in (x:(fst f), snd f)

    contradiction :: Formula -> Bool
    contradiction (Bin And (Not a) b) = (a == b)
    contradiction (Bin And a (Not b)) = (a == b)
    contradiction _ = False
        
    hasFreeVariable :: Variable -> Formula -> Bool
    hasFreeVariable x (Atom (Pred _ xs)) = any (hasTerm x) xs
        where   hasTerm y (Function _ ys) = any (hasTerm y) ys
                hasTerm y z = y == z
    hasFreeVariable _ (Atom (Prop _)) = False
    hasFreeVariable x (Not a) = hasFreeVariable x a
    hasFreeVariable x (Bin _ a b) = hasFreeVariable x a || hasFreeVariable x b
    hasFreeVariable x (Quan _ y a) = if x == y then False else hasFreeVariable x a

    substituteTerm :: Formula -> Variable -> Variable -> Formula
    substituteTerm (Quan q y a) t x
        | y == t && hasFreeVariable x prev = Atom (Prop $ (show t) ++ " is not free to " ++ (show x))
        | y == x = Quan q t (substituteTerm a t x)
        | otherwise = Quan q y (substituteTerm a t x)
        where prev = (Quan q y a)
    substituteTerm (Not a) t x = Not (substituteTerm a t x)
    substituteTerm (Bin f a b) t x = Bin f (substituteTerm a t x) (substituteTerm b t x)
    substituteTerm (Atom (Pred p ys)) t x = Atom (Pred p (map (sub t x) ys))
        where   sub t x (Function f ys) = if x == y then t else Function f (map (sub t x) ys)
                    where y = (Function f ys)
                sub t x y = if x == y then t else y
    substituteTerm a _ _ = a

    data Deduction = Ded [Deduction] Formula
    
    elimAnd :: Deduction -> Bool -> Deduction
    elimAnd (Ded ds (Bin And a b)) bool = Ded [prev] (if bool then a else b)
        where prev = Ded ds (Bin And a b)

    intrAnd :: Deduction -> Deduction -> Deduction
    intrAnd (Ded ds1 a) (Ded ds2 b) = Ded prevs (Bin And a b)
        where prevs = [Ded ds1 a, Ded ds2 b]
    
    elimOr :: Deduction -> Deduction -> Deduction -> Deduction
    elimOr (Ded ds1 (Bin Or a b)) (Ded ds2 c) (Ded ds3 d) = 
        if c == d then Ded prevs c
        else Ded [] (Atom (Prop "Two cases must have same conclusion."))
        where prevs = [Ded ds1 (Bin Or a b), Ded ds2 c, Ded ds3 d]
    
    intrOr :: Deduction -> Formula -> Deduction
    intrOr (Ded ds a) b = Ded [Ded ds a] (Bin Or a b)
    
    elimNot :: Deduction -> Deduction
    elimNot (Ded ds (Not (Not a))) = Ded [prev] a
        where prev = Ded ds (Not (Not a))
    
    intrNot :: Deduction -> Formula -> Deduction
    intrNot (Ded ds a) b = if contradiction a then
        Ded [Ded ds a] (Not b)
        else Ded [] (Atom (Prop "Negation must be introduced through contradiction."))
        
    elimIf :: Deduction -> Deduction -> Deduction
    elimIf (Ded ds1 (Bin If a b)) (Ded ds2 c) = if a == c then
        Ded prevs b
        else Ded [] (Atom (Prop "Invalid implication elimination."))
        where prevs = [Ded ds1 (Bin If a b), Ded ds2 c]

    intrIf :: Deduction -> Formula -> Deduction
    intrIf (Ded ds b) a = Ded [Ded ds b] (Bin If a b)

    elimIff :: Deduction -> Deduction -> Deduction
    elimIff (Ded ds1 (Bin Iff a b)) (Ded ds2 c)
        | a == c = Ded prevs b
        | b == c = Ded prevs a
        | otherwise = Ded [] (Atom (Prop "Invalid equivalence elimination."))
        where prevs = [Ded ds1 (Bin Iff a b), Ded ds2 c]

    intrIff :: Deduction -> Deduction -> Deduction
    intrIff (Ded ds1 a) (Ded ds2 b) = Ded prevs (Bin Iff a b)
        where prevs = [Ded ds1 a, Ded ds2 b]
        
    elimAll :: Deduction -> Variable -> Deduction
    elimAll (Ded ds (Quan All x a)) t = Ded [prev] (substituteTerm a t x)
        where prev = Ded ds (Quan All x a)

    intrAll :: Deduction -> Variable -> Deduction
    intrAll (Ded ds a) x =  if any (hasFreeVariable x) (getAssumptions prev) then
                                Ded [] (Atom (Prop $ "Some assumptions had " ++ (show x) ++ " as a free variable"))
                            else Ded [prev] (Quan All x a)
        where prev = Ded ds a
    
    elimExists :: Deduction -> Deduction -> Deduction
    elimExists (Ded ds1 (Quan Exists x a)) (Ded ds2 b) =
        if not (hasFreeVariable x b) || not (any (hasFreeVariable x) (getAssumptions (Ded ds2 b))) then
            Ded [Ded ds1 (Quan Exists x a), Ded ds2 b] b
        else    Ded [] (Atom (Prop $ "Some assumptions had " ++ (show x) ++ " as a free variable"))
    
    intrExists :: Deduction -> Formula -> Deduction
    intrExists (Ded ds a1) (Quan Exists x a2) =
            if (substituteTerm a2 (findTerm1 a1 a2 x) x) == a1 then
                Ded [Ded ds a1] (Quan Exists x a2)
            else Ded [] (Atom (Prop "Invalid term substitution"))
        where   findTerm1 (Bin _ c1 d1) (Bin _ c2 d2) y
                    | c1 /= c2 = findTerm1 c1 c2 y
                    | d1 /= d2 = findTerm1 d1 d2 y
                    | otherwise = y
                findTerm1 (Not c) (Not d) y = findTerm1 c d y
                findTerm1 (Quan _ t c) (Quan _ tt d) y = if t /= tt then t else findTerm1 c d y
                findTerm1 (Atom (Pred _ cs)) (Atom (Pred _ ds)) y = findTerm2 cs ds y
                    where   findTerm2 ((Function f []):az) ((Function g []):bs) y = findTerm2 az bs y
                            findTerm2 ((Function f (a:az)):fs) ((Function g (b:bs)):gs) y =
                                if y == (Function g (b:bs)) && y /= (Function f (a:az)) then Function f az
                                else findTerm2 ((Function f az):fs) ((Function g bs):gs) y
                            findTerm2 (a:az) (b:bs) y = if y == b && y /= a then a else findTerm2 az bs y
                            findTerm2 _ _ y = y
                findTerm1 _ _ y = y
    
    getAssumptions :: Deduction -> [Formula]
    getAssumptions d = assum d []
        where   assum (Ded [] a) disc = if elem a disc then [] else [a]
                assum (Ded [Ded ds1 (Bin Or a b), Ded ds2 c1, Ded ds3 c2] c3) disc =
                        (assum (Ded ds1 (Bin Or a b)) disc) `union`
                        (assum (Ded ds2 c1) (if bool then a:disc else disc)) `union`
                        (assum (Ded ds3 c2) (if bool then b:disc else disc))
                    where bool = c1 == c2 && c2 == c3
                assum (Ded [Ded ds a] (Not b)) disc =
                    assum (Ded ds a) (if contradiction a then b:disc else disc)
                assum (Ded [Ded ds b1] (Bin If a b2)) disc =
                    assum (Ded ds b1) (if b1 == b2 then a:disc else disc)
                assum (Ded [Ded ds1 a1, Ded ds2 b1] (Bin Iff a2 b2)) disc =
                        (assum (Ded ds1 a1) (if bool then b1:disc else disc)) `union`
                        (assum (Ded ds2 b1) (if bool then a1:disc else disc))
                    where bool = a1 == a2 && b1 == b2
                assum (Ded [Ded ds1 (Quan Exists x a), Ded ds2 b1] b2) disc =
                        (assum (Ded ds1 (Quan Exists x a)) disc) `union`
                        (assum (Ded ds2 b1) (if bool then a:disc else disc))
                    where bool = b1 == b2 && not (null ds2)
                assum (Ded ds _) disc = foldl step [] ds
                    where step xs d = union xs (assum d disc)
        --where   myFold [] prev _ = prev
        --        myFold (d:ds) prev disc = myFold ds (prev `union` (assum d disc)) disc
        
    assume :: Formula -> Deduction
    assume a = Ded [] a
    
    instance Show Deduction where
        show (Ded ds a) = (show $ getAssumptions (Ded ds a)) ++ " |-> " ++ (show a)
