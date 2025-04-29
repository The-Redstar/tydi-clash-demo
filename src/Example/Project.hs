-- @createDomain@ below generates a warning about orphan instances, but we like
-- our code to be warning-free.
{-# OPTIONS_GHC -Wno-orphans #-}

module Example.Project where

import Clash.Prelude

import Tydi.Data
import qualified Tydi.Data.Prefix as P
import Tydi.LStream
import Tydi.PStream
import Shockwaves
import Tydi.Synthesis
import Optics.Core hiding ((:>), Index)

data JsonField = CountField | WordField deriving (Show, Generic, Display, Split)

type CharThroughput = 16
type StrThroughput = 4
type PrinterTimeout = 20
type CharStream       = Synth (Dim (C 1) CharThroughput () Char)
type JsonStream       = Synth (Dim' 2 (C 5) 1 () (Group ("field" >:: JsonField :&: "value" >:: Union ("int" >:: Int :|: "string" >:: Dim CInherit StrThroughput () Char))))
type WordStream       = Synth (Dim (C 5) 1 () (Group ("count" >:: Int :&: "word" >:: Dim CInherit StrThroughput () Char)))
type WordScoreStream  = Synth (Dim (C 5) 1 () Int)
type ScoreStream      = Synth (New (C 5) 1 () Int)

-- send out [char<16>]
memoryReader :: (HiddenClockResetEnable dom) => Signal dom (Reverse CharStream) -> Signal dom CharStream
memoryReader = undefined


data ParseState = AwaitingBlock | AwaitingToken | ReadingToken | ReadToken | ReadingVal | ReadingInt | ReadingStr | ReadStr

-- turn chars into [[token:int|[char <4>]]]
jsonParser :: (HiddenClockResetEnable dom) => (Signal dom CharStream, Signal dom (Reverse JsonStream)) -> (Signal dom (Reverse CharStream), Signal dom JsonStream)
jsonParser = undefined

-- turn [[token,int|string]] into [(int,string)] - note that count MUST be first
wordGrouper :: (HiddenClockResetEnable dom) => (Signal dom JsonStream, Signal dom (Reverse WordStream)) -> (Signal dom (Reverse JsonStream), Signal dom WordStream)
wordGrouper = undefined

wordGrader :: (HiddenClockResetEnable dom) => (Signal dom WordStream, Signal dom (Reverse WordScoreStream)) -> (Signal dom (Reverse WordStream), Signal dom WordScoreStream)
wordGrader = unbundle . mealy go (0,0) . bundle
  where
    go :: (Int,Int) -> (WordStream, Reverse WordScoreStream) -> ((Int,Int),(Reverse WordStream, WordScoreStream))
    go (mult,acc) (in_stream,out_ready) = ((mult',acc'),(in_ready,out_stream))
      where
        count_in = view _stream in_stream
        word_in = view (_child % _field @"word" % _stream) in_stream
        out_ready' = view _stream out_ready

        in_ready = set _stream count_ready' $
                   set (_child % _field @"word" % _stream) word_ready' (forceX undefined :: Reverse WordStream)
        out_stream = set _stream out_stream' (forceX undefined :: WordScoreStream)

        (mult',count_ready') = case count_in of
          Transfer tf | Just pref <- getDataSliced tf -> (view (_field @"count") $ P.head pref, Ready)
          _ -> (mult,NotReady)

        lastLetter = maybe False (last . getLast) $ getTransfer word_in
        lastBlock  = maybe False (head . getLast) $ getTransfer word_in --needs to be propagated and may arrive later
        out_stream'
          | lastLetter = Transfer $ fromSlice (Just $ P.prefix 0 $ acc'':>Nil) (lastBlock:>Nil) ()
          | lastBlock  = Transfer $ fromSlice Nothing (lastBlock:>Nil) ()
          | otherwise  = NoTransfer
        word_ready' = if isValid word_in && not (isValid out_stream' && out_ready'==Ready) then Ready else NotReady
        acc'' = (acc +) $ (mult' *) $ maybe 0 (sum . P.map letterScore) (getTransfer word_in >>= getDataSliced)
        acc' = if word_ready'==Ready then
                 if lastLetter then 0 else acc''
               else acc

        letterScore c = case c of
          'A' -> 1
          'B' -> 2
          'C' -> 3
          _   -> 0

scoreAccumulator :: (HiddenClockResetEnable dom) => (Signal dom WordScoreStream, Signal dom (Reverse ScoreStream)) -> (Signal dom (Reverse WordScoreStream), Signal dom ScoreStream)
scoreAccumulator = unbundle . mealy go 0 . bundle
  where
    go :: Int -> (WordScoreStream, Reverse ScoreStream) -> (Int, (Reverse WordScoreStream, ScoreStream))
    go acc (in_stream, out_ready) = (acc',(in_ready,outstream))
      where
        in_stream' = view _stream in_stream -- all of this would not be required when using PStream directly
        out_ready' = view _stream out_ready
        in_ready = set _stream in_ready' (forceX undefined :: Reverse WordScoreStream)
        outstream = set _stream outstream' (forceX undefined :: ScoreStream)

        isLast = maybe False (head . getLast) $ getTransfer in_stream'
        in_ready' = if isValid in_stream' && not isLast || (out_ready'==Ready) then Ready else NotReady -- accept unless blocked by next station
        acc'' = acc + maybe 0 P.head (getTransfer in_stream' >>= getDataSliced) -- take add value if present
        acc' = if in_ready'==Ready then
                 if isLast then 0 else acc'' -- if last, 0, else
               else
                 acc'
        outstream' = if isLast then Transfer $ fromSlice (Just $ P.prefix 0 $ acc'':>Nil) Nil () else NoTransfer


scorePrinter :: (HiddenClockResetEnable dom) => Signal dom ScoreStream -> (Signal dom (Reverse ScoreStream), Signal dom (Maybe Int))
scorePrinter scores = unbundle $ mealy go 0 scores
  where
    go :: Index PrinterTimeout -> ScoreStream -> (Index PrinterTimeout,(Reverse ScoreStream,Maybe Int))
    go i scores' = (i',(ready,o))
      where
        o = if i==0 then P.head <$> (getTransfer (view _stream scores') >>= getDataSliced) else Nothing
        i' = if i==maxBound then 0 else i+1
        ready :: Reverse ScoreStream
        ready = set _stream (if i==0 then Ready else NotReady) (forceX undefined :: Reverse ScoreStream)
    -- o scores' = case view _stream scores' of
    --   Transfer tf -> (!! 0) <$> getDataStrobed tf
    --   _ -> Nothing


(<->) :: ((a,d) -> (b,c)) -> ((c,f) -> (d,e)) -> ((a,f) -> (b,e))
(<->) p q (a,f) = (b,e)
  where
    (b,c) = p (a,d)
    (d,e) = q (c,f)






-- Create a domain with the frequency of your input clock. For this example we used
-- 50 MHz.
createDomain vSystem{vName="Dom50", vPeriod=hzToPeriod 50e6}

-- | @topEntity@ is Clash@s equivalent of @main@ in other programming languages.
-- Clash will look for it when compiling "Example.Project" and translate it to
-- HDL. While polymorphism can be used freely in Clash projects, a @topEntity@
-- must be monomorphic and must use non- recursive types. Or, to put it
-- hand-wavily, a @topEntity@ must be translatable to a static number of wires.
--
-- Top entities must be monomorphic, meaning we have to specify all type variables.
-- In this case, we are using the @Dom50@ domain, which we created with @createDomain@
-- and we are using 8-bit unsigned numbers.
topEntity ::
  Clock Dom50 ->
  Reset Dom50 ->
  Enable Dom50 ->
  Signal Dom50 (Maybe Int)
topEntity = exposeClockResetEnable main

-- To specify the names of the ports of our top entity, we create a @Synthesize@ annotation.
-- {-# ANN topEntity
--   (Synthesize
--     { t_name = "accum"
--     , t_inputs = [ PortName "CLK"
--                  , PortName "RST"
--                  , PortName "EN"
--                  , PortName "DIN"
--                  ]
--     , t_output = PortName "DOUT"
--     }) #-}

-- Make sure GHC does not apply any optimizations to the boundaries of the design.
-- For GHC versions 9.2 or older, use: {-# NOINLINE topEntity #-}
{-# OPAQUE topEntity #-}

-- combine all modules
main ::
  (HiddenClockResetEnable dom) =>
  Signal dom (Maybe Int)
main = o
  where
    (r2,o) = scorePrinter f2
    (r1,f2) = (jsonParser <-> wordGrouper <-> wordGrader <-> scoreAccumulator) (f1,r2)
    f1 = memoryReader r1

-- [```]--f1->[````]--f2->[`````]
-- |MEM|      |PROC|      |PRINT|--o-->
-- [___]<-r1--[____]<-r2--[_____]
