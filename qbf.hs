{-# LANGUAGE RankNTypes #-}

import Data.Hashable (Hashable)
import qualified Data.HashMap.Strict as HM

import Control.Lens
import Control.Monad.Trans.State
import Control.Monad.IO.Class (liftIO)

import System.Mem.StableName (StableName)
import qualified System.Mem.StableName as SN

data Bit =
    And Bit Bit |
    Or Bit Bit |
    Not Bit |
    TrueE |
    FalseE |
    Exists (Bit -> Bit) |
    ForAll (Bit -> Bit) |

    UnsafeVar Int

varName :: Int -> String
varName n = "v" ++ show n

build :: Bit -> IO ()
build expr = do
    n <- evalStateT (build' expr) (HM.empty, 0)
    putStrLn $ varName n
  where
    getVar :: Monad m => StateT (a, Int) m Int
    getVar = do
        output <- use _2
        _2 %= (+1)
        return output

    insertName :: (Eq k, Hashable k, Monad m) => k -> v -> StateT (HM.HashMap k v, a) m ()
    insertName k v =
        _1 %= HM.insert k v

    build' :: Bit -> StateT (HM.HashMap (StableName Bit) Int, Int) IO Int
    build' e = do
        name <- liftIO $ SN.makeStableName e
        entry <- uses _1 (HM.lookup name)
        case entry of
            Just i -> return i
            Nothing -> do
                v <- getVar
                insertName name v
                case e of
                    And x y -> do
                        x' <- build' x
                        y' <- build' y
                        liftIO $ putStrLn $ varName v ++ " = and(" ++ varName x' ++ ", " ++ varName y' ++ ")"
                        return v
                    Or x y -> do
                        x' <- build' x
                        y' <- build' y
                        liftIO $ putStrLn $ varName v ++ " = or(" ++ varName x' ++ ", " ++ varName y' ++ ")"
                        return v
                    Not x -> do
                        x' <- build' x
                        liftIO $ putStrLn $ varName v ++ " = not(" ++ varName x' ++ ")"
                        return v
                    TrueE -> do
                        liftIO $ putStrLn $ varName v ++ " = true"
                        return v
                    FalseE -> do
                        liftIO $ putStrLn $ varName v ++ " = false"
                        return v
                    Exists f -> do
                        v1 <- getVar
                        let var = UnsafeVar v1
                        name1 <- liftIO $ SN.makeStableName var
                        insertName name1 v1
                        liftIO $ putStrLn $ "exists " ++ varName v1
                        build' $ f var
                    ForAll f -> do
                        v1 <- getVar
                        let var = UnsafeVar v1
                        name1 <- liftIO $ SN.makeStableName var
                        insertName name1 v1
                        liftIO $ putStrLn $ "forall " ++ varName v1
                        build' $ f var
                    UnsafeVar x -> do
                        return x

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (a:b:xs) = (a, b) : pairs xs

unpairs :: [(a, a)] -> [a]
unpairs [] = []
unpairs ((a,b):xs) = a : b : unpairs xs

class BitEq a where
    bitEq :: a -> a -> Bit

    nBitEq :: a -> a -> Bit
    nBitEq a b = Not (bitEq a b)

class BitEq a => BitOrd a where
    bitLt :: a -> a -> Bit

    bitGt :: a -> a -> Bit
    bitGt = flip bitLt

    bitLe :: a -> a -> Bit
    bitLe a b = Not (bitGt a b)

    bitGe :: a -> a -> Bit
    bitGe a b = Not (bitLt a b)

class Bitable a where
    bits :: a -> [Bit]
    fromBits :: [Bit] -> a

instance BitEq Bit where
    bitEq x y = Not (x `xor` y)

instance BitEq a => BitEq [a] where
    bitEq [] [] = TrueE
    bitEq (x:xs) (y:ys) =
        (x `bitEq` y) `And` (xs `bitEq` ys)

instance (BitEq a, BitEq b) => BitEq (a, b) where
    bitEq (a, b) (p, q) = bitEq a p `And` bitEq b q

instance (BitEq a, BitEq b, BitEq c, BitEq d) => BitEq (a, b, c, d) where
    bitEq (a, b, c, d) (p, q, r, s) =
        bitEq a p `And`
        bitEq b q `And`
        bitEq c r `And`
        bitEq d s

instance Bitable Bit where
    bits a = [a]
    fromBits [a] = a

instance BitOrd Bit where
    bitLt a b =
        Not a `And` b

xor :: Bit -> Bit -> Bit
xor x y = (x `Or` y) `And` (Not (x `And` y))

implies :: Bit -> Bit -> Bit
implies a b = Not (a `And` (Not b))

exists_ :: Int -> ([Bit] -> Bit) -> Bit
exists_ 0 f = f []
exists_ n f = Exists (\x -> exists_ (n - 1) (\xs -> f (x : xs)))

forall_ :: Int -> ([Bit] -> Bit) -> Bit
forall_ 0 f = f []
forall_ n f = ForAll (\x -> forall_ (n - 1) (\xs -> f (x : xs)))

halfAdder :: Bit -> Bit -> (Bit, Bit)
halfAdder y z = (y `And` z, y `xor` z)

majority3 :: Bit -> Bit -> Bit -> Bit
majority3 x y z =
    (x `And` y) `Or`
    (x `And` z) `Or`
    (y `And` z)

adder :: Bit -> Bit -> Bit -> (Bit, Bit)
adder x y z =
    let
        l = x `xor` y `xor` z
        h = majority3 x y z
    in
        (h, l)

add :: [Bit] -> [Bit] -> [Bit]
add [y] [z] =
    let
        (p, q) = halfAdder y z
    in
        [p, q]
add (y:ys) (z:zs) =
    let
        x:xs = add ys zs
        (p, q) = adder x y z
    in
        [p, q] ++ xs

mux2 :: Bit -> (Bit, Bit) -> Bit
mux2 x (p, q) =
    (x `And` p) `Or`
    ((Not x) `And` q)

mux :: [Bit] -> [Bit] -> Bit
mux [] [y] = y
mux (x:xs) y =
    mux xs $ map (mux2 x) $ pairs y

permute2 :: Bit -> (Bit, Bit) -> (Bit, Bit)
permute2 s x = (mux2 s x, mux2 (Not s) x)

permute4 :: (Bit, Bit, Bit, Bit) -> ((Bit, Bit), (Bit, Bit)) -> ((Bit, Bit), (Bit, Bit))
permute4 (a, b, c, d) (p, q) =
    let
        p' = permute2 a p
        q' = permute2 b q
        ((w, x), (y, z)) = (p', q')
        (p'', q'') = ((w, y), (x, z))
        p''' = permute2 c p''
        q''' = permute2 d q''
    in
        (p''', q''')

comparator :: (BitOrd a, Bitable a) => (a, a) -> (a, a)
comparator (x, y) =
    let
        x' = bits x
        y' = bits y
        c = bitLt x y
        (x'', y'') = unzip $ map (permute2 c) $ zip x' y'
        x''' = fromBits x''
        y''' = fromBits y''
    in
        (x''', y''')

compMerge :: (BitOrd a, Bitable a) => [a] -> [a] -> [a]
compMerge [] [] = []
compMerge [x] [y] =
    let
        (a, b) = comparator (x, y)
    in
        [a, b]
compMerge x y =
    let
        (u, v) = unzip $ pairs x
        (p, q) = unzip $ pairs y
        (l:x') = compMerge u p
        (h:y') = reverse $ compMerge v q
        y'' = reverse y'
        m = unpairs $ map comparator $ zip x' y''
    in
        [l] ++ m ++ [h]

compSort :: (BitOrd a, Bitable a) => [a] -> [a]
compSort [x] = [x]
compSort input =
    let
        (a, b) = unzip (pairs input)
        a' = compSort a
        b' = compSort b
    in
        compMerge a' b'

isSorted :: (BitOrd a) => [a] -> Bit
isSorted [] = TrueE
isSorted [x] = TrueE
isSorted (x:x':xs) =
    (x `bitLe` x') `And` isSorted (x':xs)

main = do
    build $
        forall_ 16 (\x ->
            forall_ 4 (\y ->
                exists_ 4 (\z ->
                    mux y (compSort x) `bitEq` mux z x
                )
            )
        )
