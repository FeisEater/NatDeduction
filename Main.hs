    module Main where
    
    import NatDeduction
    import Data.List
    import Data.Maybe
    import qualified Data.Map as Map
    import System.IO
    
    main = do
        putStrLn "Natural deduction simulator 2014"
        getCommand []

    commands = Map.fromList [   ("assume", addAssumption),
                                ("forget", removeDed),
                                ("elimAnd", eAnd),
                                ("intrAnd", iAnd),
                                ("elimOr", eOr),
                                ("intrOr", iOr),
                                ("elimNot", eNot),
                                ("intrNot", iNot),
                                ("elimIf", eIf),
                                ("intrIf", iIf),
                                ("elimIff", eIff),
                                ("intrIff", iIff),
                                ("elimAll", eAll),
                                ("intrAll", iAll),
                                ("elimExists", eExists),
                                ("intrExists", iExists)]
                                
    getCommand deds = do
        putStr "> "
        hFlush stdout
        line <- getLine
        let cmd = getArg line 0
        if Map.member cmd commands
            then do
                let deductions = (fromJust $ Map.lookup cmd commands) deds line
                putStrLn $ unlines $ enumerate $ map show deductions
                getCommand deductions
            else do
                if cmd == "print"
                    then do
                        putStrLn $ dedTree $ deds!!(read $ getArg line 1)
                        getCommand deds
                    else getCommand deds
    
    enumerate :: [String] -> [String]
    enumerate xs = map enum $ zip [0..(length xs)] xs
        where enum (a,b) = (show a) ++ ": " ++ b
    
    getArg cmd n = (words cmd)!!n
    
    lastArg cmd n = let (_,formula) = splitAt n (words cmd) in unwords formula
    
    deleteAt :: Int -> [Deduction] -> [Deduction]
    deleteAt _ [] = []
    deleteAt n xs = let (a,b) = splitAt n xs
                    in a ++ (if null b then [] else tail b)

    addAssumption :: [Deduction] -> String -> [Deduction]
    addAssumption deds cmd = deds ++ [assume formula]
        where formula = readFormula $ lastArg cmd 1
    
    removeDed :: [Deduction] -> String -> [Deduction]
    removeDed deds cmd = deleteAt (read $ getArg cmd 1) deds
    
    eAnd :: [Deduction] -> String -> [Deduction]
    eAnd deds cmd = (deleteAt a $ deds) ++ [elimAnd (deds!!a) b]
        where   a = read $ getArg cmd 1
                b = getArg cmd 2 /= "r"

    iAnd :: [Deduction] -> String -> [Deduction]
    iAnd deds cmd = dedDed intrAnd deds cmd

    eOr :: [Deduction] -> String -> [Deduction]
    eOr deds cmd = (deleteAt a . deleteAt b . deleteAt c $ deds) ++ 
                    [elimOr (deds!!a) (deds!!b) (deds!!c)]
        where   a = read $ getArg cmd 1
                b = read $ getArg cmd 2
                c = read $ getArg cmd 3
                
    iOr :: [Deduction] -> String -> [Deduction]
    iOr deds cmd = dedForm intrOr deds cmd
                
    eNot :: [Deduction] -> String -> [Deduction]
    eNot deds cmd = (deleteAt a $ deds) ++ [elimNot (deds!!a)]
        where a = read $ getArg cmd 1
        
    iNot :: [Deduction] -> String -> [Deduction]
    iNot deds cmd = dedForm intrNot deds cmd

    eIf :: [Deduction] -> String -> [Deduction]
    eIf deds cmd = dedDed elimIf deds cmd

    iIf :: [Deduction] -> String -> [Deduction]
    iIf deds cmd = dedForm intrIf deds cmd
                
    eIff :: [Deduction] -> String -> [Deduction]
    eIff deds cmd = dedDed elimIff deds cmd
    
    iIff :: [Deduction] -> String -> [Deduction]
    iIff deds cmd = dedDed intrIff deds cmd
    
    eAll :: [Deduction] -> String -> [Deduction]
    eAll deds cmd = dedTerm elimAll deds cmd
    
    iAll :: [Deduction] -> String -> [Deduction]
    iAll deds cmd = dedTerm intrAll deds cmd
    
    eExists :: [Deduction] -> String -> [Deduction]
    eExists deds cmd = dedDed elimExists deds cmd
    
    iExists :: [Deduction] -> String -> [Deduction]
    iExists deds cmd = dedForm intrExists deds cmd
    
    dedDed :: (Deduction -> Deduction -> Deduction) -> [Deduction] -> String -> [Deduction]
    dedDed func deds cmd = (deleteAt a . deleteAt b $ deds) ++ [func (deds!!a) (deds!!b)]
        where   a = read $ getArg cmd 1
                b = read $ getArg cmd 2

    dedForm :: (Deduction -> Formula -> Deduction) -> [Deduction] -> String -> [Deduction]
    dedForm func deds cmd = (deleteAt a $ deds) ++ [func (deds!!a) formula]
        where   a = read $ getArg cmd 1
                formula = readFormula $ lastArg cmd 2

    dedTerm :: (Deduction -> Variable -> Deduction) -> [Deduction] -> String -> [Deduction]
    dedTerm func deds cmd = (deleteAt a $ deds) ++ [func (deds!!a) formula]
        where   a = read $ getArg cmd 1
                formula = readTerm $ lastArg cmd 2

    dedTree :: Deduction -> String
    dedTree d = printTree $ reverse $ bwsInStack [(0,d)]
        where   bwsInStack ((n, Ded parents a):ds) = 
                    (n,a):(bwsInStack $ ds ++ (reverse $ map (giveLvl $ n+1) parents))
                bwsInStack [] = []
                giveLvl n d = (n,d)
                printTree ((x,a):(y,b):xs) = (show a) ++ bool ++ printTree ((y,b):xs)
                    where bool = if x == y then "   " else "\n"
                printTree ((x,a):[]) = show a