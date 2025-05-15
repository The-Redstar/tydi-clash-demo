{-# OPTIONS_GHC -fconstraint-solver-iterations=20 #-}
-- @createDomain@ below generates a warning about orphan instances, but we like
-- our code to be warning-free.
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Example.Project where

import Clash.Prelude

import Tydi.Data
import qualified Tydi.Data.Prefix as P
import Tydi.LStream
import Tydi.PStream
import Shockwaves
import Tydi.Synthesis
import Optics.Core hiding ((:>), Index)
-- import Data.Proxy (Proxy(..))
import Data.Maybe (fromJust)
import Data.Typeable
import Data.Char
import qualified Data.Text as Text
import qualified Clash.Explicit.Signal

import Example.Input
import Shockwaves.Trace as WFT

-- import Optics.Lens

data JsonField = CountField | WordField | OtherField deriving (Show, Generic, Display, Split, Eq, NFDataX, BitPack)

type CharThroughput = 16
type StrThroughput = 4
type PrinterTimeout = 20
type CharStream       = Synth (Dim (C 1) CharThroughput () Char) -- TODO v make the string stream unsynced
type JsonStream       = Synth (Dim' 2 (C 5) 1 () (Group ("field" >:: JsonField :&: "value" >:: Union ("int" >:: Int :|: "string" >:: Dim CInherit StrThroughput () Char))))
type WordStream       = Synth (Dim (C 5) 1 () (Group ("count" >:: Int :&: "word" >:: Dim CInherit StrThroughput () Char)))
type WordScoreStream  = Synth (Dim (C 5) 1 () Int)
type ScoreStream      = Synth (New (C 5) 1 () Int)

newtype CharInt a = CharInt a
instance BitPack (CharInt Char) where
  type BitSize (CharInt Char) = BitSize Int
  pack (CharInt a) = pack $ ord a
  unpack x= CharInt $ chr $ unpack x

deriving via (CharInt Char) instance BitPack Char

mealy'
  :: ( HiddenClockResetEnable dom
     , NFDataX s
     , BitPack s
     , Typeable s
     , Display s
     , Split s )
  => String
  -> (s -> i -> (s,o))
  -- ^ Transfer function in mealy machine form: @state -> input -> (newstate,output)@
  -> s
  -- ^ Initial state
  -> (Signal dom i -> Signal dom o)
  -- ^ Synchronous sequential function with input and output matching that
  -- of the mealy machine
mealy' = hideClockResetEnable mealy''

mealy''
  :: ( KnownDomain dom
     , NFDataX s
     , BitPack s
     , Typeable s
     , Display s
     , Split s )
  => Clock dom
  -- ^ 'Clock' to synchronize to
  -> Reset dom
  -> Enable dom
  -- ^ Global enable
  -> String
  -> (s -> i -> (s,o))
  -- ^ Transfer function in mealy machine form: @state -> input -> (newstate,output)@
  -> s
  -- ^ Initial state
  -> (Signal dom i -> Signal dom o)
  -- ^ Synchronous sequential function with input and output matching that
  -- of the mealy machine
mealy'' clk rst en name f iS =
  \i -> let (s',o) = unbundle $ f <$> s <*> i
            s      = WFT.traceSignal1 name $ Clash.Explicit.Signal.register clk rst en iS s'
        in  o
{-# INLINABLE mealy'' #-}


convertReady :: PStreamReady c n d u e -> PStreamReady c' n' d' u' e'
convertReady = \case
  Ready -> Ready
  NotReady -> NotReady


data ReaderState = Reading (Index NFiles) Int | Done deriving (Show,Generic,NFDataX,Eq,BitPack,Typeable,Display,Split)
-- send out [char<16>]
memoryReader :: (HiddenClockResetEnable dom) => Signal dom (Reverse CharStream) -> Signal dom CharStream
memoryReader = mealy' "memoryReaderState" go (Reading 0 0)
  where
    go :: ReaderState -> Reverse CharStream -> (ReaderState,CharStream)
    go Done _ = (Done, set _stream NoTransfer (ensureSpine undefined :: CharStream))
    go state@(Reading file index) ready = (state',out)
      where
        blocksize :: Int
        blocksize = fromIntegral $ natVal $ Proxy @CharThroughput
        (filelen,fileStart) = files !! file
        isReady = view _stream ready == Ready
        state' = if isReady then nextState else state
        (nextState,isLast) = if index+blocksize < filelen then
                      (Reading file (index+blocksize), False)
                    else
                      ( if file < maxBound then
                          Reading (file+1) 0
                        else Done
                      , True)
        out = set _stream out' (ensureSpine undefined::CharStream)
        out' = Transfer $ fromSlice (Just dat) (isLast:>Nil) ()
        dat = P.prefix -- $ repeat @CharThroughput '?'
                (fromIntegral $ (min blocksize (filelen-index))-1)
                (take (SNat @CharThroughput) $ rotateLeft fileData (index+fileStart))


type TokenParserState = (Int,Bool,Bool)
data ParserState =
    AwaitingStart
  | AwaitingBlock
  | AwaitingToken
  | ReadingToken TokenParserState
  | ReadToken JsonField
  | ReadingVal JsonField
  | ReadingInt JsonField Int
  | ReadingStr
  | ReadVal
  | ParsingDone
  deriving (Generic,NFDataX,Show,Typeable,BitPack,Display,Split)
-- AwaitingStart '[' -> AwaitingBlock
-- AwaitingBlock '{' -> AwaitingToken
-- AwaitingToken '"' -> ReadingToken
-- ReadingToken  '"' -> ReadToken; SET TOKEN
-- ReadingToken   c  -> ReadingToken; TOKENPARSES
-- ReadToken     ':' -> ReadingVal
-- ReadingVal    \d  -> ReadingInt
-- ReadingVal    '"' -> ReadingStr; SEND!
-- ReadingInt    !\d -> ReadVal; SEND AND CONTINUE!!! (i.e. ',' send & await token, '}' send +end and await block, c send)
-- ReadingStr    '"' -> ReadVal; SEND2 END
-- ReadingStr     c  -> ReadingStr; SEND2 c
-- ReadVal       ',' -> AwaitingToken
-- ReadVal       '}' -> AwaitingBlock
-- AwaitingBlock ']' -> Done

-- for each, output (NEW_STATE, Maybe MSG, Maybe LAST, Maybe Char, Maybe LAST2)
-- merge values for more efficient bandwidth usage? -> MSG+LAST, LAST+LAST', do 2 streams separately
-- turn into 2 C8 streams?
-- collapse onto C5 using buffer?
-- compatibility function to determine if it should be a slice


-- thanks Lucas
-- packVec :: (KnownNat n) => Vec n (Maybe a) -> Vec n (Maybe a)
-- packVec = foldr f (repeat Nothing)
--  where
--   f (Just a) acc = Just a +>> acc
--   f Nothing acc = acc

packVec2 :: (KnownNat n) => Vec n (Maybe a, Maybe b) -> Vec n (Maybe a, Maybe b)
packVec2 = foldr f (repeat (Nothing,Nothing))
 where
  f (Nothing,Nothing) acc = acc
  f x acc = x +>> acc


shiftLeft :: (Enum i, KnownNat n)
           => Vec n a
           -> a
           -> i
           -> Vec n a
shiftLeft xs new i = map f (iterateI (+1) i')
  --map ((xs !!) . (`mod` len)) (iterateI (+1) i')
  where
    f j = if j<len then xs!!j else new
    i'  = fromEnum i
    len = length xs
{-# INLINE shiftLeft #-}


-- turn chars into [[token:int|[char <4>]]]
jsonParser :: (HiddenClockResetEnable dom) => (Signal dom CharStream, Signal dom (Reverse JsonStream)) -> (Signal dom (Reverse CharStream), Signal dom JsonStream)
jsonParser = unbundle . mealy' "jsonParserState" go (AwaitingStart,0,0,undefined,undefined,undefined) . bundle -- take data strobed, map statemachine function to appliccable fields, collect two streams, shift to front, put in queue, send as many through as possible
  where
    --go :: (ParserState, Int,Int) -> (CharStream, Reverse JsonStream) -> ((ParserState, Int,Int),(Reverse CharStream, JsonStream))
    go (state,sendFieldI,sendStringI,_,_,_) (streamIn,readyOut)
      | Transfer tfIn <- (view _stream streamIn)
      = let
          readyIn = set _stream readyChar $ ensureSpine (undefined::CharStream)
          streamOut = set _stream streamField $
                      set (_child % _field @"value" % _field @"string" % _stream) streamString $
                      ensureSpine (undefined::JsonStream)

          readyField = view _stream readyOut
          readyString = view (_child % _field @"value" % _field @"string" % _stream) readyOut

          -- streamString = undefined
          -- readyChar = undefined

          sendFieldI''  = if readyField==Ready  then sendFieldI  + head fieldEvents else sendFieldI -- next value unless reset
          sendStringI'' = if readyString==Ready then sendStringI + head stringEvents else sendStringI-- next value unless reset

          doneSendingField  = (not $ isValid streamField ) || (readyField ==Ready && (fieldEvents  !! head fieldEvents)  == 0) --not sending or just completing last transfer
          doneSendingString = (not $ isValid streamString) || (readyString==Ready && (stringEvents !! head stringEvents) == 0)

          sendFieldI'  = if readyChar==Ready then 0 else sendFieldI'' --next value unless reset
          sendStringI' = if readyChar==Ready then 0 else sendStringI''

          readyChar = if doneSendingField && doneSendingString then Ready else NotReady

          actions = postscanl (\(s,_) cM -> maybe (s,n4) (statemachine s) cM) (state,undefined) (getDataStrobed tfIn)
          state' = if readyChar==Ready then fst $ last actions else state
          (a,b,c,d) = unzip4 $ map snd actions
          fieldData  = packVec2 $ zip a b --left aligned maybe vec of things to send in the field stream
          stringData = packVec2 $ zip c d --left aligned maybe vec of things to send in the string stream

          {-
          field stream can send one word and at most LAST directly after it

          string stream can send up to StringThroughput characters at once, followed by at most one LAST
          -}

          shiftedFieldData = shiftLeft fieldData (Nothing,Nothing) sendFieldI
          (fieldEvents,fieldDatas,fieldLast) = takeEvents 1 shiftedFieldData
          streamField = if head fieldEvents > 0 then
              Transfer $ fromSlice fieldStreamData (maybe (repeat False) id (head fieldLast)) ()
            else
              NoTransfer
          fieldStreamData = if head fieldDatas > 0 then
              Just $ P.prefix (fromIntegral $ head fieldDatas - 1) $ map (fromJust . fst) $ take d1 shiftedFieldData
            else Nothing

          shiftedStringData = shiftLeft stringData (Nothing,Nothing) sendStringI
          (stringEvents,stringDatas,stringLast) = takeEvents (fromInteger . natVal $ Proxy @StrThroughput) shiftedStringData
          streamString = if head stringEvents > 0 then
              Transfer $ fromSlice stringStreamData (maybe (repeat False) id (head stringLast)) ()
            else
              NoTransfer
          -- stringStreamData :: Maybe (P.Prefix 4 Char)
          stringStreamData = if head stringDatas > 0 then
              Just $ P.prefix (fromIntegral $ head stringDatas - 1) $ map (fromJust . fst) $ take (SNat @StrThroughput) shiftedStringData
            else Nothing
        in ((state',sendFieldI',sendStringI',actions,shiftedFieldData,fieldEvents), (readyIn,streamOut))

    go state _ -- (streamIn,_) | NoTransfer <- (view _stream streamIn)
      = (state, (readyIn,streamOut))
      where
        readyIn = set _stream NotReady $ ensureSpine (undefined::CharStream)
        streamOut = set _stream NoTransfer $
                    set (_child % _field @"value" % _field @"string" % _stream) NoTransfer $
                    ensureSpine (undefined::JsonStream)

    takeEvents :: Int -> Vec n (Maybe a, Maybe b) -> (Vec n Int, Vec n Int, Vec n (Maybe b))
    takeEvents lanes = unzip3 . postscanr f (0,0,Nothing)
      where
        f (Nothing,Nothing) (_,_,_) = (0,0,Nothing)
        f (Just _ ,Nothing) (events,datas,lst)
          | datas<lanes
          = (events+1,datas+1,lst) -- TODO: if data+1>lanes, cut off end instead
        f (Just _ ,Nothing) (events,datas,_)
          | events==datas
          = (events,datas,Nothing) -- drop last (D,L) pair
        f (Just _ ,Nothing) (events,datas,_)
          = (events-1,datas,Nothing) -- drop last (D,-) and (-,L) pairs
        f (Nothing,Just l ) (_,_,_) = (1,0,Just l)
        f (Just _ ,Just l ) (_,_,_) = (1,1,Just l)


    statemachine
      :: ParserState
      -> Char
      -> ( ParserState
         , ( Maybe (DataType (StreamType (JsonStream)))
           , Maybe (Vec (Dims (StreamType (JsonStream))) Bool)
           , Maybe Char
           , Maybe (Vec 3 Bool)))
    statemachine state input = case (state,input) of
      (AwaitingStart , '[') -> (AwaitingBlock,n4)
      (AwaitingBlock , '{') -> (AwaitingToken,n4)
      (AwaitingToken , '"') -> (ReadingToken s0,n4)
      -- (AwaitingToken ,  _ ) -> (AwaitingToken,n4)
      (ReadingToken s, '"') -> (ReadToken t,n4) -- SET TOKEN
                              where t = getToken s
      (ReadingToken s,  c ) -> (ReadingToken s',n4) -- ADD TO TOKEN
                              where s' = updateToken c s
      (ReadToken t   , ':') -> (ReadingVal t,n4)
      (ReadingVal t  ,  d ) | isDigit d -> (ReadingInt t $ num d,n4)
      (ReadingVal t  , '"') -> (ReadingStr,(Just msg,Nothing,Nothing,Nothing)) --SEND token:string
                              where msg = set (_field @"field") t $
                                          set (_field @"value") (mkVariant @"string" ()) $
                                          ensureSpine undefined
      (ReadingInt t n,  d ) | isDigit d -> (ReadingInt t $ n*10 + (num d),n4)
      (ReadingInt t n,  c ) -> (state',(Just msg,lst,Nothing,lst2)) -- SEND AND CONTINUE!!! (i.e. ',' send & await token, '}' send +end and await block, c send)
                              where (state',lst,lst2) = afterVal c
                                    msg = set (_field @"field") t $
                                          set (_field @"value") (mkVariant @"int" n) $
                                          ensureSpine undefined
      (ReadingStr    , '"') -> (ReadVal,(Nothing,Nothing,Nothing,Just (False:>False:>True:>Nil))) -- SEND2 END
      (ReadingStr    ,  c ) -> (ReadingStr,(Nothing,Nothing,Just c,Nothing)) -- SEND2 c
      (ReadVal       ,  c ) -> (state',(Nothing,lst,Nothing,lst2))
                              where (state',lst,lst2) = afterVal c
      -- (ReadVal       , ',') -> (AwaitingToken,n4)
      -- (ReadVal       , '}') -> (AwaitingBlock,n4) -- SEND END
      (AwaitingBlock , ']') -> (AwaitingStart,(Nothing,Just $ True:>False:>Nil,Nothing,Just $ True:>False:>False:>Nil)) -- SEND END
      _                     -> (state,n4)

    afterVal '}' = (AwaitingBlock, Just (False:>True:>Nil),Just (False:>True:>False:>Nil))
    afterVal ',' = (AwaitingToken, Nothing, Nothing)
    afterVal  _  = (ReadVal, Nothing, Nothing)
    n4=(Nothing,Nothing,Nothing,Nothing)
    -- isDigit d = '0'<=d && d<='9'
    num '0' = 0
    num '1' = 1
    num '2' = 2
    num '3' = 3
    num '4' = 4
    num '5' = 5
    num '6' = 6
    num '7' = 7
    num '8' = 8
    num '9' = 9
    num  _  = undefined

    -- token reader functions
    s0 :: (Int,Bool,Bool)
    s0 = (0,True,True) --initial state
    updateToken c (i,canBeWord,canBeCount) = (i',cbw,cbc)-- update state with character
      where i'=i+1
            cbw = canBeWord  && i<4 && c==($(listToVecTH "word" ) !! i)
            cbc = canBeCount && i<5 && c==($(listToVecTH "count") !! i)
    getToken (i,canBeWord,canBeCount) = --get token from state
      if      i==4 && canBeWord  then WordField
      else if i==5 && canBeCount then CountField
      else                            OtherField

-- turn [[token,int|string]] into [(int,string)] - note that count MUST be first
data GrouperMode = ListeningMain | ListeningString deriving (Show,Generic,NFDataX,Eq,Display,Split,BitPack,Typeable)
wordGrouper :: (HiddenClockResetEnable dom) => (Signal dom JsonStream, Signal dom (Reverse WordStream)) -> (Signal dom (Reverse JsonStream), Signal dom WordStream)
wordGrouper = unbundle . mealy' "GrouperMode" go (ListeningMain,False,1) . bundle
  where
    go :: (GrouperMode,Bool,Int) -> (JsonStream,Reverse WordStream) -> ((GrouperMode,Bool,Int),(Reverse JsonStream,WordStream))
    go (activeStream,sendingString,count) (stream_in,ready_out) = ((activeStream',sendingString',count'),(ready_in,stream_out))
      where
        -- lenses for stream bundles
        _fld :: Lens (StreamNode p h) (StreamNode p' h) p p'
        _fld = _stream
        _string
         :: (FieldType "string" (FieldType "value" v) ~ StreamNode b h,
            HasField "value" v, HasField "string" (FieldType "value" v)) => Lens (StreamNode p v) (StreamNode p v) b b
        _string = _child % _field @"value" % _field @"string" % _stream
        _count = _stream
        _word :: (FieldType "word" v ~ StreamNode b h, HasField "word" v) =>
                  Lens (StreamNode p v) (StreamNode p v) b b
        _word = _child % _field @"word" % _stream

        -- unpacking stream bundles
        fieldStream = view _fld stream_in
        stringStream :: StreamType (FieldType "string" (FieldType "value" (ChildType JsonStream)))
        stringStream = view _string stream_in
        ready_in :: Reverse JsonStream
        ready_in = set _fld fieldReady $
                   (set _string stringReady $
                   ensureSpine (undefined::Reverse JsonStream) ::Reverse JsonStream)

        countReady = view _count ready_out
        -- wordReady :: PStreamReady (C 5) 4 2 () Char
        wordReady = view _word ready_out
        stream_out :: WordStream
        stream_out = set _count countStream $
                     set _word wordStream $
                     ensureSpine (undefined::WordStream)

        paused = (isValid countStream && countReady==NotReady) || (isValid wordStream && wordReady==NotReady)

        fieldReady :: StreamType (Reverse JsonStream)
        fieldReady  = if paused || activeStream==ListeningString then NotReady else Ready
        stringReady :: PStreamReady (C 5) 4 3 () Char
        stringReady = if emptyStringTransfer then convertReady wordReady else
                      if paused || activeStream==ListeningMain then NotReady else
                      if sendingString then case wordReady of
                        Ready -> Ready
                        NotReady -> NotReady
                      else Ready
        emptyStringTransfer = case stringStream of --in case a "last" bit is being sent on its own, absorb it
          Transfer tf | Nothing <- getDataSliced tf -> True
          _                                         -> False

        countStream :: StreamType WordStream
        countStream = if activeStream==ListeningString then NoTransfer else
                      case fieldStream of
                        Transfer tf | True <- (last . getLast) tf -> Transfer $ fromSlice (Just . P.full $ msg :>Nil) (take d1 $ getLast tf) ()
                        Transfer tf | True <- (head . getLast) tf -> Transfer $ fromSlice Nothing (take d1 $ getLast tf) ()
                        _ -> NoTransfer
                      -- if lastField then Transfer $ fromStrobed (Just  :>Nil) (getLast )
        msg :: DataType (StreamType WordStream)
        msg = set (_field @"count") count'' (ensureSpine undefined :: DataType (StreamType WordStream))
        wordStream :: PStream (C 5) 4 2 () Char
        wordStream = case stringStream of
                       Transfer tf | Nothing <- getDataSliced tf -> Transfer $ fromSlice Nothing lst ()
                        where lst = (head $ getLast tf) :> (last $ getLast tf) :> Nil
                       _ -> if activeStream==ListeningString && sendingString then
                              case stringStream of
                                Transfer tf | a:>_:>b:>Nil <- getLast tf -> Transfer $ fromSlice (getDataSliced tf) (a:>b:>Nil) ()
                                _ -> NoTransfer
                            else NoTransfer


        -- lastBlock = maybe False (head . getLast) $ getTransfer fieldStream
        lastField = maybe False (last . getLast) $ getTransfer fieldStream

        count'' = if activeStream==ListeningString then count else
                  case fieldStream of
                    Transfer tf | Just g :> Nil <- getDataStrobed tf,
                                  CountField <- getField @"field" g,
                                  Just x <- getVariant @"int" $ getField @"value" g
                                  -> x
                    _             -> count
        count' = if paused then count else
                 if lastField && countReady==Ready then 1 else count''

        activeStream' = if paused then activeStream else
                        if activeStream==ListeningMain && receivingString then ListeningString else
                        if activeStream==ListeningString && lastLetter then ListeningMain else
                        activeStream
        sendingString' = if paused then sendingString else
                        if activeStream==ListeningMain && receivingWord then True else
                        if activeStream==ListeningString && lastLetter then False else
                        sendingString

        lastLetter = case stringStream of
                       Transfer tf | True <- (last . getLast) tf -> True
                       _ -> False
        (receivingWord,receivingString) = case fieldStream of
                                            Transfer tf | Just g :> Nil <- getDataStrobed tf
                                                        , Just _ <- getVariant @"string" $ getField @"value" g
                                                        -> (True,getField @"field" g==WordField)
                                            _           -> (False,False)

        -- count' = case fieldStream of
        --   Transfer tf | Just (Group $ L CountField :&: L val):>Nil <- getDataStrobed tf, Just x <- getVariant @"int" val -> x -- get count value
        --   _ -> count
        -- count'' = if maybe False (or . getLast) $ getTransfer fieldStream then 1 else count' -- reset after completion of block

        -- readingString' = if paused then readingString
        --                  else if maybe False (or . getLast) $ getTransfer stringStream then
        --                    False
        --                  else case fieldStream of
        --                    Transfer tf | Just (Group $ L WordField :&: L val):>Nil <- getDataStrobed tf, Just _ <- getVariant @"string" val -> True
        --                    _ -> readingString

        -- (activeStream',wordStream,) = case activeStream of
        --   ListeningMain -> ...
        --   ListeningString -> ..


{-

when sending data (word or ) and that stream is not ready, pause

when (count,int) comes in:
  set count
when (word,string) comes in:
  transfer (count,string) [start rediricting to string]
when last0:
  transfer last0


case ListeningMain
  stringReady = NotReady
  wordStream = NoTransfer

  if receiving count
    fieldReady = Ready
    set count
  elif receiving string
    fieldReady = Ready
    activeStream'= ListeningString
    if receiving word:
      sendingString = True
  else
    fieldReady = Ready

  if last fieldStream
    countStream = tf count'
    if countReady
      reset count
  elif lastBlock
    fieldReady=Ready
    countStream = tf last
  else
    countStream = NoTransfer

case ListeningString
  countStream = NoTransfer
  fieldReady = NotReady

  if sendingString
    stringReady = wordReady
    wordStream = stringStream
  else
    stringReady = Ready
    wordStream = NoTransfer

  if last letter
    activeStream' = ListeningMain



-}

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
                   set (_child % _field @"word" % _stream) word_ready' (ensureSpine undefined :: Reverse WordStream)
        out_stream = set _stream out_stream' (ensureSpine undefined :: WordScoreStream)

        (mult',count_ready') = case count_in of
          Transfer tf | Just pref <- getDataSliced tf -> (view (_field @"count") $ P.head pref, Ready)
          Transfer tf -> (mult,Ready)
          _ -> (mult,NotReady)

        lastLetter = maybe False (last . getLast) $ getTransfer word_in
        lastBlock  = maybe False (head . getLast) $ getTransfer word_in --needs to be propagated and may arrive later
        out_stream'
          | lastLetter = Transfer $ fromSlice (Just $ P.prefix 0 $ acc'':>Nil) (lastBlock:>Nil) ()
          | lastBlock  = Transfer $ fromSlice Nothing (lastBlock:>Nil) ()
          | otherwise  = NoTransfer
        word_ready' = if isValid word_in && not (isValid out_stream' && out_ready'==NotReady) then Ready else NotReady
        acc'' = (acc +) $ (mult' *) $ maybe 0 (sum . P.map letterScore) (getTransfer word_in >>= getDataSliced)
        acc' = if word_ready'==Ready then
                 if lastLetter then 0 else acc''
               else acc

        letterScore c = case c of
          'A' -> 10
          'B' -> 20
          'C' -> 30
          _   -> 1

scoreAccumulator :: (HiddenClockResetEnable dom) => (Signal dom WordScoreStream, Signal dom (Reverse ScoreStream)) -> (Signal dom (Reverse WordScoreStream), Signal dom ScoreStream)
scoreAccumulator = unbundle . mealy go 0 . bundle
  where
    go :: Int -> (WordScoreStream, Reverse ScoreStream) -> (Int, (Reverse WordScoreStream, ScoreStream))
    go acc (in_stream, out_ready) = (acc',(in_ready,outstream))
      where
        in_stream' = view _stream in_stream -- all of this would not be required when using PStream directly
        out_ready' = view _stream out_ready
        in_ready = set _stream in_ready' (ensureSpine undefined :: Reverse WordScoreStream)
        outstream = set _stream outstream' (ensureSpine undefined :: ScoreStream)

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
        ready = set _stream (if i==0 then Ready else NotReady) (ensureSpine undefined :: Reverse ScoreStream)
    -- o scores' = case view _stream scores' of
    --   Transfer tf -> (!! 0) <$> getDataStrobed tf
    --   _ -> Nothing



trace :: (
    HiddenClockResetEnable dom
  , BitPack (a,b)
  , NFDataX (a,b)
  , Typeable (a,b)
  , Display (a,b)
  , Split (a,b)
  ) => String -> (Signal dom a,Signal dom b) -> (Signal dom b,Signal dom a)
trace lbl (a,b) = swap <$> unbundle $ WFT.traceSignal1 lbl $ bundle (a,b)
  where swap (x,y) = (y,x)


-- (<->) :: ((a,d) -> (b,c)) -> ((c,f) -> (d,e)) -> ((a,f) -> (b,e))
-- (<->) p q (a,f) = (b,e)
--   where
--     (b,c) = p (a,d)
--     (d,e) = q (c,f)

(<->) :: ((Signal dom a,Signal dom d) -> (Signal dom b,Signal dom c)) -> ((Signal dom c,Signal dom f) -> (Signal dom d,Signal dom e)) -> ((Signal dom a,Signal dom f) -> (Signal dom b,Signal dom e))
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
  Signal Dom50 Output
topEntity = exposeClockResetEnable mainJson

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
type Output = (Bool,Bool) -- Maybe Int
mainJson ::
  (HiddenClockResetEnable dom) =>
  Signal dom Output
mainJson = WFT.traceSignal1 "output" o
  where
    -- o :: Signal dom (Maybe Int)
    -- f1 :: Signal dom (CharStream)
    -- r1 :: Signal dom (Reverse CharStream)
    -- f2 :: Signal dom (ScoreStream)
    -- r2 :: Signal dom (Reverse ScoreStream)

    (r2,o) = acceptor f2--scorePrinter f2
    middle =
      (   trace "characters"
      <-> jsonParser
      <-> trace "json"
      <-> wordGrouper
      <-> trace "words"
      <-> wordGrader
      <-> trace "wordScores"
      <-> scoreAccumulator
      <-> trace "accum"
      )
    -- middle = (trace "characters" <-> jsonParser <-> trace "json" <-> wordGrouper <-> trace "words" <-> wordGrader <-> trace "wordScores" <-> scoreAccumulator <-> trace "accum")
    (r1,f2) = middle (f1,r2)
    f1 = memoryReader r1
    -- x = _idk (f1,r1,f2,r2,o,middle)

-- [```]--f1->[````]--f2->[`````]
-- |MEM|      |PROC|      |PRINT|--o-->
-- [___]<-r1--[____]<-r2--[_____]


-- createDomain vSystem{vName="Dom50", vPeriod=hzToPeriod 50e6}

maintrace :: IO ()
maintrace = do
  let output = topEntity (clockGen @Dom50) (resetGen @Dom50) enableGen
  let output' = seq (sampleN @Dom50 30 output) output
  vcddata <- WFT.dumpVCD (0, 120) output' ["output","characters","json","words","wordScores"]
  case vcddata of
    Left msg ->
      error msg
    Right (vcd,types,trans) ->
      do writeFile "trace/waveform.vcd" $ Text.unpack vcd
         writeFile "trace/waveform.types.json" $ Text.unpack types
         writeFile "trace/waveform.trans.json" $ Text.unpack trans





-- debugging

acceptor :: (HiddenClockResetEnable dom, AlwaysReady (Reverse a),Eq a,Default a) => Signal dom a -> (Signal dom (Reverse a), Signal dom (Bool,Bool))
acceptor streamIn = (const alwaysReady <$> streamIn, bundle ((def==) <$> streamIn,clksign streamIn))
  where clksign = mealy (\s _ -> (not s,s)) False

class AlwaysReady a where
  alwaysReady :: a
instance AlwaysReady () where
  alwaysReady = ()
instance (AlwaysReady a) => AlwaysReady (Group a) where
  alwaysReady = Group $ alwaysReady @a
instance (AlwaysReady a, AlwaysReady b) => AlwaysReady (a :&: b) where
  alwaysReady = alwaysReady @a :&: alwaysReady @b
instance (AlwaysReady a) => AlwaysReady (lbl>::a) where
  alwaysReady = L $ alwaysReady
instance (AlwaysReady c, AlwaysReady p) => AlwaysReady (StreamNode p c) where
  alwaysReady = StreamNode (alwaysReady) (alwaysReady)
instance AlwaysReady (PStreamReady c n d u e) where
  alwaysReady = Ready









