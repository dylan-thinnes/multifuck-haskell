{-# LANGUAGE NamedFieldPuns #-}
module Main where

import Prelude hiding (Right, Left)
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Word

import           Data.Map.Strict ((!?))
import qualified Data.Map.Strict as M
import System.Environment (getArgs)

import Debug.Trace

-- UTILS
unjust :: String -> Maybe a -> a
unjust err Nothing = error err
unjust _ (Just a) = a

mayToZero :: (Eq a, Num a) => Maybe a -> a
mayToZero Nothing = 0
mayToZero (Just x) = x

zeroToMay :: (Eq a, Num a) => a -> Maybe a
zeroToMay 0 = Nothing
zeroToMay x = Just x

justify :: (Eq a, Num a) => (a -> a) -> Maybe a -> Maybe a
justify f = zeroToMay . f . mayToZero

-- MAIN
main :: IO ()
main = do
    args <- getArgs
    let path = head args

    raw <- readFile path
    let startingTape = tokenize raw

    finalState <- run $ tapeToState startingTape
    print $ pointer finalState
    print $ memory finalState
    pure ()

-- Tokens & Tokenizer
data Tok = Incr | Decr | Left | Right | StartLoop | EndLoop | Input | Output | RotateUp | RotateDown
    deriving (Show, Read)

data TokMode = Comment | NoComment

tokenize :: String -> Tape Tok
tokenize = fromList . go NoComment
    where
        go _ [] = []
        go _ ('#':cs) = go Comment cs
        go Comment ('\n':cs) = go NoComment cs
        go Comment (c:cs) = go Comment cs
        go NoComment (c:cs) =
            case cToTok c of
              Nothing -> go NoComment cs
              Just tok -> tok : go NoComment cs
        cToTok '+' = Just Incr
        cToTok '-' = Just Decr
        cToTok '[' = Just StartLoop
        cToTok ']' = Just EndLoop
        cToTok '<' = Just Left
        cToTok '>' = Just Right
        cToTok ',' = Just Input
        cToTok '.' = Just Output
        cToTok '*' = Just RotateUp
        cToTok '/' = Just RotateDown
        cToTok _ = Nothing

-- Program tape & construction/querying/movement thereof
type Tape a = ([a],[a])

fromList :: [a] -> Tape a
fromList xs = ([], xs)

focus :: Tape a -> Maybe a
focus (_, c:_) = Just c
focus (_, [])  = Nothing

right, left :: Tape a -> Maybe (Tape a)
right = fmap snd . pright
left = fmap snd . pleft

pright, pleft :: Tape a -> Maybe (a, Tape a)
pright (as, b:bs) = Just (b, (b:as, bs))
pright (as, [])   = Nothing
pleft (a:as, bs) = Just (a, (as, a:bs))
pleft ([], bs)   = Nothing

-- Running of instructions
type Cell = Int
type Instr = Tok
newtype Addr = Addr { _unaddr :: M.Map Int Int }
    deriving (Eq, Ord, Show)
type Memory = M.Map Addr Cell
data State = State { tape :: Tape Tok, memory :: Memory, pointer :: Addr, direction :: Int }
    deriving (Show)
tapeToState tape = State { tape, memory = M.empty, pointer = Addr M.empty, direction = 0 }

getPtrVal :: State -> Cell
getPtrVal State { pointer, memory } = fromMaybe 0 $ memory !? pointer

modifyPtrVal :: (Cell -> Cell) -> State -> State
modifyPtrVal f state@State { pointer, memory } =
    state { memory = M.alter (justify f) pointer memory }

modifyAddr :: (Int -> Int) -> Int -> Addr -> Addr
modifyAddr f axis (Addr m) = Addr $ M.alter (justify f) axis m
incrAddr, decrAddr :: Int -> Addr -> Addr
incrAddr = modifyAddr succ
decrAddr = modifyAddr pred

editTape :: (Tape Tok -> Maybe (Tape Tok)) -> State -> Maybe State
editTape f state@State { tape } = fmap (\t -> state { tape = t }) (f tape)
nextInstr, prevInstr :: State -> Maybe State
nextInstr = editTape right
prevInstr = editTape left

step :: Instr -> State -> IO (Maybe State)
step instr state@State { tape, memory, direction, pointer } =
    case instr of
      Incr -> pure $ nextInstr $ modifyPtrVal succ state
      Decr -> pure $ nextInstr $ modifyPtrVal pred state
      Left -> pure $ nextInstr $ state { pointer = decrAddr direction pointer }
      Right -> pure $ nextInstr $ state { pointer = incrAddr direction pointer }
      StartLoop ->
        pure $
            if getPtrVal state == 0
               then nextInstr =<< editTape (Just . toEndLoop) =<< nextInstr state
               else nextInstr state
      EndLoop -> pure $ editTape (Just . toStartLoop) =<< prevInstr state
      Input -> do
          inp <- readLn
          pure $ nextInstr $ modifyPtrVal (const inp) state
      Output -> do
          print $ getPtrVal state
          pure $ nextInstr state
      RotateUp -> pure $ nextInstr $ state { direction = direction + 1 }
      RotateDown -> pure $ nextInstr $ state { direction = direction - 1 }

run :: State -> IO State
run state@State { tape } = do
    case focus tape of
      Nothing -> pure state
      Just instr -> do
        mnext <- step instr state
        case mnext of
          Nothing -> pure state
          Just next -> run next

-- Move to start/end of loop
toEndLoop :: Tape Tok -> Tape Tok
toEndLoop = helper 0
    where
    helper :: Int -> Tape Tok -> Tape Tok
    helper depth tape =
        case unjust "No matching end of loop." $ pright tape of
          (EndLoop, r)
            | depth == 0 -> tape
            | otherwise -> helper (depth - 1) r
          (StartLoop, r) -> helper (depth + 1) r
          (_, r) -> helper depth r

toStartLoop :: Tape Tok -> Tape Tok
toStartLoop = helper 0
    where
    helper :: Int -> Tape Tok -> Tape Tok
    helper depth tape =
        case unjust "No matching start of loop." $ pleft tape of
          (StartLoop, l)
            | depth == 0 -> unjust "No matching start of loop." $ left tape
            | otherwise -> helper (depth - 1) l
          (EndLoop, l) -> helper (depth + 1) l
          (_, l) -> helper depth l
