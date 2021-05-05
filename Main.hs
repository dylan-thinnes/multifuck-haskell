{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
module Main where

import Prelude
import Data.Maybe (mapMaybe, fromMaybe, catMaybes)
import Data.List (intercalate)
import Data.Word
import System.Random
import Control.Monad (guard)

import           Data.Map.Strict ((!?))
import qualified Data.Map.Strict as M
import qualified Data.Array as A
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
    print $ memory finalState
    pure ()

-- Tokens & Tokenizer
data Tok
    = Incr | Decr
    | MoveLeft | MoveRight
    | StartLoop | EndLoop
    | Input | Output
    | RotateUp | RotateDown
    | Fork
    | Debug
    | Roll
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
        cToTok '<' = Just MoveLeft
        cToTok '>' = Just MoveRight
        cToTok ',' = Just Input
        cToTok '.' = Just Output
        cToTok '*' = Just RotateUp
        cToTok '/' = Just RotateDown
        cToTok '&' = Just Fork
        cToTok '!' = Just Debug
        cToTok '?' = Just Roll
        cToTok _ = Nothing

-- Program tape & construction/querying/movement thereof
type Tape a = A.Array Int a

fromList :: [a] -> Tape a
fromList xs = A.listArray (0, length xs - 1) xs

-- Running of instructions
type Cell = Int
type Instr = Tok

newtype Addr = Addr { _unaddr :: M.Map Int Int }
    deriving (Eq, Ord)

instance Show Addr where
    show (Addr m) = fromMaybe "(|)" $ do
        let assocs = M.toAscList m
        (lowestDim, _) <- M.lookupMin m
        (highestDim, _) <- M.lookupMax m
        let underZeroDims = [lowestDim.. -1]
        let aboveZeroDims = [0..highestDim]
        let underZeroText = intercalate ", " $ map (\d -> show $ fromMaybe 0 $ m !? d) underZeroDims
        let aboveZeroText = intercalate ", " $ map (\d -> show $ fromMaybe 0 $ m !? d) aboveZeroDims
        pure $ concat ["(", underZeroText, "|", aboveZeroText, ")"]

type Memory = M.Map Addr Cell
data State = State { tape :: !(Tape Tok), memory :: !Memory, threads :: ![Thread], coldThreads :: ![Thread] }
    deriving (Show)

data Thread = Thread { instructionPointer :: !Int, memoryPointer :: !Addr, direction :: !Int }
    deriving (Show)

tapeToState :: Tape Tok -> State
tapeToState tape =
    State
        { tape
        , memory = M.empty
        , threads =
            [ Thread { instructionPointer = 0, memoryPointer = Addr M.empty, direction = 0 }
            ]
        , coldThreads = []
        }

getPtrVal :: Memory -> Addr -> Cell
getPtrVal memory memoryPointer =
    fromMaybe 0 $ memory !? memoryPointer

modifyPtrVal :: (Cell -> Cell) -> Addr -> Memory -> Memory
modifyPtrVal f = M.alter (justify f)

modifyAddr :: (Int -> Int) -> Int -> Addr -> Addr
modifyAddr f axis (Addr m) = Addr $ M.alter (justify f) axis m
incrAddr, decrAddr :: Int -> Addr -> Addr
incrAddr = modifyAddr succ
decrAddr = modifyAddr pred

currInstr :: Tape Tok -> Thread -> Maybe Tok
currInstr tape Thread { instructionPointer } = do
    guard $ snd (A.bounds tape) >= instructionPointer
    guard $ fst (A.bounds tape) <= instructionPointer
    pure $ tape A.! instructionPointer

nextInstr, prevInstr :: Tape Tok -> Thread -> Maybe Thread
nextInstr tape thread@Thread { instructionPointer } = do
    let t' = thread { instructionPointer = instructionPointer + 1 }
    currInstr tape t'
    pure t'
prevInstr tape thread@Thread { instructionPointer } = do
    let t' = thread { instructionPointer = instructionPointer - 1 }
    currInstr tape t'
    pure t'

stepPure :: Instr -> Tape Tok -> Memory -> Thread -> Maybe (Memory -> Memory, Bool, Thread)
stepPure instr tape memory thread@Thread { direction, memoryPointer } =
    case instr of
      Incr -> (modifyPtrVal succ memoryPointer, False,) <$> nextInstr tape thread
      Decr -> (modifyPtrVal pred memoryPointer, False,) <$> nextInstr tape thread
      MoveLeft -> (id, False,) <$> nextInstr tape (thread { memoryPointer = decrAddr direction memoryPointer })
      MoveRight -> (id, False,) <$> nextInstr tape (thread { memoryPointer = incrAddr direction memoryPointer })
      StartLoop -> (id, False,) <$>
        if getPtrVal memory memoryPointer == 0
           then nextInstr tape =<< toEndLoop tape =<< nextInstr tape thread
           else nextInstr tape thread
      EndLoop -> (id, False,) <$> (toStartLoop tape =<< prevInstr tape thread)
      RotateUp -> (id, False,) <$> nextInstr tape (thread { direction = direction + 1 })
      RotateDown -> (id, False,) <$> nextInstr tape (thread { direction = direction - 1 })
      Fork -> (id, True,) <$> nextInstr tape thread

step :: Instr -> Tape Tok -> Memory -> Thread -> IO (Maybe (Memory -> Memory, Bool, Thread))
step instr tape memory thread@Thread { direction, memoryPointer } =
    case instr of
      Input -> do
          inp <- readLn
          pure $ (modifyPtrVal (const inp) memoryPointer, False,) <$> nextInstr tape thread
      Output -> do
          print $ getPtrVal memory memoryPointer
          pure $ (id, False,) <$> nextInstr tape thread
      Debug -> do
          print (instr, memory, thread)
          pure $ (id, False,) <$> nextInstr tape thread
      Roll -> do
          r <- randomRIO (0, getPtrVal memory memoryPointer - 1)
          pure $ (modifyPtrVal (const r) memoryPointer, False,) <$> nextInstr tape thread
      _ -> pure $ stepPure instr tape memory thread

autoinstrStep :: Tape Tok -> Memory -> Thread -> IO (Maybe (Memory -> Memory, Bool, Thread))
autoinstrStep tape memory thread = do
    case currInstr tape thread of
      Nothing -> pure Nothing
      Just instr -> step instr tape memory thread

run1 :: State -> IO (Either State State)
run1 state@State { tape, memory, threads, coldThreads } =
    if null threads
       then pure $ Left state
       else do
        threadSteps <- traverse (autoinstrStep tape memory) threads
        let (memoryAlterers, forks, updatedThreads) = unzip3 $ catMaybes threadSteps
        let newlyForkedThreads = [ thread | (True, thread) <- zip forks updatedThreads ]
        pure $ Right $ state
            { memory = foldl (flip ($)) memory memoryAlterers
            , threads = coldThreads ++ updatedThreads
            , coldThreads = newlyForkedThreads
            }

run :: State -> IO State
run state = do
    next <- run1 state
    case next of
      Left state -> pure state
      Right state -> run state

-- Move to start/end of loop
toEndLoop :: Tape Tok -> Thread -> Maybe Thread
toEndLoop tape = helper 0
    where
    helper :: Int -> Thread -> Maybe Thread
    helper depth thread =
        case currInstr tape thread of
          Just EndLoop
            | depth == 0 -> pure thread
            | otherwise -> helper (depth - 1) =<< nextInstr tape thread
          Just StartLoop -> helper (depth + 1) =<< nextInstr tape thread
          Just _ -> helper depth =<< nextInstr tape thread
          Nothing -> Nothing

toStartLoop :: Tape Tok -> Thread -> Maybe Thread
toStartLoop tape = helper 0
    where
    helper :: Int -> Thread -> Maybe Thread
    helper depth thread =
        case currInstr tape thread of
          Just StartLoop
            | depth == 0 -> pure thread
            | otherwise -> helper (depth - 1) =<< prevInstr tape thread
          Just EndLoop -> helper (depth + 1) =<< prevInstr tape thread
          Just _ -> helper depth =<< prevInstr tape thread
          Nothing -> Nothing
