    import Mainn
    import NatDeduction
    
    avna = elimNot 
        (intrNot 
            (intrAnd 
                (intrOr 
                    (intrNot 
                        (intrAnd 
                            (intrOr (assume $ readFormula "a") $ readFormula "-a")
                            (assume $ readFormula "-(a | -a)"))
                        $ readFormula "a")
                    $ readFormula "a")
                (assume $ readFormula "-(a | -a)"))
            $ readFormula "-(a | -a)")
    
    superavna = intrAnd avna avna
    
    printt d = putStrLn $ printDeds $ spaceOut False $ reverse $ bwsInStack d