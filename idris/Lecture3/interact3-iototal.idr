%default total

data Command : Type -> Type where
     PutStr : String -> Command ()
     GetStr : Command String

%name Command cmd

data InfIO : Type where
     Do : Command a -> (a -> Inf InfIO) -> InfIO

(>>=) : Command a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

loopy : InfIO
loopy = do PutStr "What is your name? "
           name <- GetStr
           PutStr ("Hello " ++ name ++ "\n")
           loopy

{- Running interactive programs -}

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetStr     = getLine

partial
run : InfIO -> IO ()
run (Do cmd f) = do res <- runCommand cmd
                    run (f res)


{- Define a way of saying when an interactive program terminates -}

data Fuel = Dry | More (Lazy Fuel)

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run_total : Fuel -> InfIO -> IO ()
run_total Dry      y = putStrLn "Out of fuel"
run_total (More x) (Do cmd f)
  = do res <- runCommand cmd
       run_total x (f res)
       
partial
forever: Fuel
forever = More forever       
