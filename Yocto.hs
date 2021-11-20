{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE LambdaCase          #-}

import           Control.Monad          hiding (fmap)
import qualified Data.Map               as Map
import           Data.Text              (Text)
import           Data.Void              (Void)
import           Plutus.Contract        as Contract
import qualified PlutusTx
import           PlutusTx.IsData
import           PlutusTx.Prelude       hiding (Semigroup(..), unless)
import           Ledger                 hiding (singleton)
import           Ledger.Constraints     as Constraints
import           Ledger.Index           as Index
import qualified Ledger.Typed.Scripts   as Scripts
import qualified Ledger.Contexts                   as Validation
import           Ledger.Value           as Value
import           Playground.Contract    (printJson, printSchemas, ensureKnownCurrencies, stage, ToSchema, NonEmpty(..) )
import           Playground.TH          (mkKnownCurrencies, mkSchemaDefinitions, ensureKnownCurrencies)
import           Playground.Types       (KnownCurrency (..))
import           Prelude                (Semigroup (..))
import           Text.Printf            (printf)
import           GHC.Generics         (Generic)
import           Data.String          (IsString (..))
import           Data.Aeson           (ToJSON, FromJSON)
import           Playground.Contract
import Distribution.Simple.Command (OptDescr(BoolOpt))
import System.Directory.Internal.Prelude (Bool(True))
import Distribution.SPDX (LicenseId(OLDAP_2_3))

data Proposal = Proposal
    { proposalStart :: !POSIXTime
    , scriptUpdate  :: !Bool
    , scriptAddr    :: Address
    , spend         :: !Bool
    , value         :: Value
    , spendAddr     :: Address
    , mint          :: !Bool
    , minted        :: Integer
    , yes           :: !Integer
    , no            :: !Integer
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Proposal

data Ownership = Ownership
    { owner        :: !PubKeyHash
    , nftSlot      :: POSIXTime
    , lastTransfer :: POSIXTime
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Ownership

data TokenTrace = TokenTrace
    { minted              :: !Integer
    , treasury            :: !Integer
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''TokenTrace

data IdMaker = AssetClass

PlutusTx.makeLift ''IdMaker

{-- | Initialise the 'TokenTrace' with specified deposits.
initialState :: Integer -> Integer -> TypedValidator -> TokenTrace
initialState mint treasure validator =
    TokenTrace
        { minted = mint
        , treasury = treasure
        } --}

data GovernanceDatum = Proposal | Ownership | TokenTrace | IdMaker
    deriving Show

{-# INLINABLE ownershipDatum #-}
ownershipDatum :: TxOut -> Maybe Ownership
ownershipDatum o = do
    dh      <- txOutDatum o
    Datum d <- findDatum dh txInfo
    PlutusTx.fromBuiltinData d

{-# INLINABLE proposalDatum #-}
proposalDatum :: TxOut -> Maybe Proposal
proposalDatum o = do
    dh      <- txOutDatum o
    Datum d <- findDatum dh txInfo
    PlutusTx.fromBuiltinData d

{-# INLINABLE traceDatum #-}
traceDatum :: TxOut -> Maybe TokenTrace
traceDatum o = do
    dh      <- txOutDatum o
    Datum d <- findDatum dh txInfo
    PlutusTx.fromBuiltinData d

{-# INLINABLE idMakerDatum #-}
idMakerDatum :: TxOut -> Maybe IdMaker
idMakerDatum o = do
    dh      <- txOutDatum o
    Datum d <- findDatum dh txInfo
    PlutusTx.fromBuiltinData d

{-# INLINABLE votingPassValidator #-}
votingPassValidator :: Address -> AssetClass -> AssetClass -> AssetClass -> AssetClass -> AssetClass -> GovernanceDatum -> BuiltinData -> ScriptContext -> Bool
votingPassValidator treasury govClass nft idMaker propclass voteclass datum r ctx =
  let
      txInfo = scriptContextTxInfo ctx

      -- We map over all of the inputs to the transaction to gather the number of votes present.
      txIns = txInfoInputs $ scriptContextTxInfo ctx
      txInValues = [txOutValue $ txInInfoResolved txIn | txIn <- txIns]
      txOuts = [tx | tx <- txInfoOutputs txInfo]
      continuingOutputs = getContinuingOutputs txInfo
      tokenValues = [assetClassValueOf val govClass | val <- txInValues]
      votes = sum tokenValues -- sum the occurrences of the tokenClass inside of txInValues.
      nftValues = [assetClassValueOf val nft | val <- txInValues]
      nftPresent = (sum nftValues > 0) -- sum the occurrences of the tokenClass inside of txInValues.
      nftTxos = [txo | txo <- txIns, (assetClassValueOf (txOutValue $ txInInfoResolved txo) nft > 0)]
      idMakers = [txo | txo <- txIns, (assetClassValueOf (txOutValue $ txInInfoResolved txo) idMaker > 0)]
      propTxos = [txo | txo <- txIns, (assetClassValueOf (txOutValue $ txInInfoResolved txo) propclass > 0)]
      proposalPresent = propTxos /= []
      voteTxos = [txo | txo <- txIns, (assetClassValueOf (txOutValue $ txInInfoResolved txo) voteclass > 0)]
      idOuts = [tx | tx <- txOuts, (assetClassValueOf (txOutValue tx) == idMaker > 0)]
      idConOuts = [tx | tx <- continuingOutputs, (assetClassValueOf (txOutValue tx) == idMaker > 0)]
  in
      noIdsLeaveScript &&
      validDatumOutputs &&
      if length idMakers > 0 then
          idMakerContinues &&
          idOuts == idConOuts &&
          not nftPresent &&
          not proposalPresent &&
          length voteTxos == 0
      else
          (not ownershipDatumPresent txInfo ||
          ensureOwnershipOutputs) &&
          ((not nftPresent ||
          -- Here we need to make sure that: There are enough votes to push the vote forward, and that there is enough of a yes:no ratio.
          (proposalPresent && -- This just makes sure that the proposal is present.
              correctScriptOutputs && -- This needs to check spending from the treasury -- Also checks any minted gov tokens -> Goes to treasury. -- Prop to burn?
              numberOfVotesMet && -- This makes sure the votes are correct.
              highEnoughRatio)) || -- Verify that only funds allow to be spent are spent. -- We don't check that the time has passed in this contract. TODO
          (not proposalPresent ||
          (oldEnoughInput &&
              correctPropOutputs)))
    where
        idMakerContinues :: Bool
        idMakerContinues =
          let
              idOut = idConOuts !! 0
              idOutDatum = idMakerDatum idOut
          in
              case idOutDatum of
                  Just d  -> True
                  Nothing -> False

        validDatumOutput :: TxOut -> Bool
        validDatumOutput tx =
          let
              idOutDatum = idMakerDatum tx
              ownerOut = ownershipDatum tx
              nftOut = traceDatum tx
              proposalOut = proposalDatum tx
          in
              case (idOutDatum, ownerOut, nftOut, proposalOut) of
                  (Nothing, Nothing, Nothing, Just p) -> True
                  (Nothing, Nothing, Just t, Nothing) -> True
                  (Nothing, Just o, Nothing, Nothing) -> oldEnoughOwnership' o
                  (Just i, Nothing, Nothing, Nothing) -> True
                  _                                   -> False
        
        validDatumOutputs :: Bool
        validDatumOutputs = [tx | tx <- continuingOutputs, (validDatumOutput tx)] == continuingOutputs

        -- We need to make sure that our tokens of type prop or of type vote are all accounted for and are returned to the script.
        noIdsLeaveScript :: Bool
        noIdsLeaveScript = [tx | tx <- txOuts, ((assetClassValueOf (txOutValue tx) propclass > 0) || (assetClassValueOf (txOutValue tx) voteclass > 0))] == [tx | tx <- continuingOutputs, ((assetClassValueOf (txOutValue tx) propclass > 0) || (assetClassValueOf (txOutValue tx) voteclass > 0))]

        -- This simply checks all of the Datum values coming from the script and if there are any then it returns true.
        ownershipDatumPresent :: Bool
        ownershipDatumPresent = [tx | tx <- txIns, (ownershipDatum (txInInfoResolved tx)) /= Nothing] /= []

        oldEnoughOwnership' :: Ownership -> Bool
        oldEnoughOwnership' o =
          let
              t = lastTransfer o
          in
              contains (from (o + 1200)) $ txInfoValidRange txInfo

        oldEnoughOwnership :: Maybe Ownership -> Maybe Proposal -> Bool
        oldEnoughOwnership o p = case o of
            Just od  ->
                case p of
                    Just pd ->
                      let
                          t = lastTransfer od
                          ps = proposalStart pd
                      in
                          contains (from t) (from ps)
                    Nothing -> False
            Nothing -> False
        
        -- This makes sure that all UTxOs containing ownership tokens are old enough to be participating in the vote that they're attending.
        oldEnoughInput :: Bool
        oldEnoughInput =
          let
              proposal = proposalDatum propTxos !! 0
          in
              [txo | txo <- voteTxos, (oldEnoughOwnership (ownershipDatum txo) proposal)] == voteTxos

        -- This checks the proposal to see if amount of time that has passed is adequate to skip the numberOfVotesMet.
        epochsPassed :: Maybe Proposal -> Bool
        epochsPassed mp = case mp of
            Just p  ->
              let
                  ps = proposalStart p
                  d5 = 4320000 -- This is 5 days in seconds x 10 for POSIX Conversion
              in
                  contains (from (ps + d5)) (txInfoValidRange txInfo)
            Nothing -> False

        -- If we add a thing to track the number of minted gov tokens into the script Datum we can use this to denote the hardset numbers. One thing at a time though right?
        numberOfVotesMet :: Bool
        numberOfVotesMet =
          let
              proposal = proposalDatum (propTxos !! 0)
              nft = traceDatum (nftTxos !! 0)
          in
              case proposal of
                  Just proposal -> case nft of
                      Just nft -> (yes proposal + no proposal) % (minted nft - treasury nft) > 5 % 10
                      Nothing  -> False
                  Nothing       -> False

        -- This just checks to see that there is enough of a ratio between yes and no.
        highEnoughRatio :: Bool
        highEnoughRatio =
          let
              proposal = proposalDatum propTxos !! 0
          in
              case proposal of
                  Just proposal -> (yes proposal % no proposal) > 51 % 49
                  Nothing       -> False
        
        validOwnerOutput' :: Ownership -> Bool
        validOwnerOutput' d = contains (txInfoValidRange txInfo) (from (lastTransfer d + 1200))
        
        validOwnerOutput :: Maybe Ownership -> Bool
        validOwnerOutput md = case md of
            Just d  -> validOwnerOutput' d
            Nothing -> False
        
        -- This makes sure that all UTxOs containing OwnershipDatum are sent to the correct place with the correct timestamps.
        -- If the UTxO is also contained in voteTxos then the time
        -- This makes sure the datum inputs from above also have the corresponding output UTxO: either at the script or at the owners address.
        -- It also requires the owners signature on the transaction for these to be spent.
        -- It also requires that the output Datum is within 120 seconds +/- of the time that the transaction is submitted on-chain.
        ensureOwnershipOutputs :: Bool
        ensureOwnershipOutputs =
          let
              ownershipInputs = [tx | tx <- txIns, (ownershipDatum (txInInfoResolved tx)) /= Nothing]
              ownershipSigned = [tx | tx <- ownershipInputs, (txSignedBy txInfo $ owner (ownershipDatum $ txInInfoResolved tx))]
              ownershipOutputDatums = [ownershipDatum tx | tx <- (TxInfoOutputs txInfo), (ownershipDatum tx) /= Nothing]
              validOutputs = [validOwnerOutput datum | datum <- ownershipOutputDatums]
          in
              ownershipInputs == ownershipSigned &&
              foldr && True validOutputs

        compareProposals' :: Proposal -> Proposal -> Bool
        compareProposals' before after =
            (proposalStart before) == (proposalStart after) &&
            (scriptUpdate before) == (scriptUpdate after) &&
            (scriptAddr before) == (scriptAddr after) &&
            (spend before) == (spend after) &&
            (value before) == (value after) &&
            (spendAddr before) == (spendAddr after) &&
            (mint before) == (mint after) &&
            (minted before) == (minted after) &&
            (yes before) <= (yes after) &&
            (no before) <= (no after) &&
            (yes after + no after) - (yes before + no before) == votes


        compareProposals :: Maybe Proposal -> Maybe Proposal -> Bool
        compareProposals before after = case before of
            Just b  -> case after of
                Just a  -> compareProposals' b a
                Nothing -> False
            Nothing -> False

        -- This function validates the updating of the proposal datum.
        correctPropOutputs :: Bool
        correctPropOutputs =
          let
              propIn = propTxos !! 0
              propOuts = [txo | txo <- (txInfoOutputs txInfo), (assetClassValueOf (txOutValue $ txo) propclass > 0)]
              propOut = propOuts !! 0
          in
              if (length propTxos) > 1 || (length propOuts) > 1 then False else
                  compareProposals (proposalDatum propIn) (proposalDatum propOut)

        checkOnePath :: Proposal -> Bool
        checkOnePath p =
          let
              spending = spend p
              minting = mint p
              updating = checkIfScriptSpent
              s = if spending then 1 else 0
              m = if minting then 1 else 0
              u = if updating then 1 else 0
          in
              s + m + u == 1

        -- The treasury must spend the right amount.
        -- No Update or Minting may occur.
        checkScriptTreasuryUse :: Proposal -> Bool
        checkScriptTreasuryUse p =
          let
              spent = value p
              spendAddress = spendAddr p
              treasuryIns = [tx | tx <- txIns, ((txOutAddress $ txInInfoResolved tx) == treasury)]
              treasuryIn = treasuryIns !! 0
              val = txOutValue treasuryIn
              spendOuts = [tx | tx <- txOuts, ((txOutAddress tx == spendAddress) && (txOutValue tx == spent) && (txOutValue tx == val))]
              mintVal = txInfoMint txInfo
              nftOuts = [tx | tx <- txOuts, (assetClassValueOf (txOutValue tx) nft > 0)]
              nftOut = nftOuts !! 0
          in -- Make sure only one in TxO for the treasury and one out for the treasury with the right value and the right address.
              -- This is going to allow for multiple outputs in the same proposal in the future. Taken out for now to reduce complexity.
              length treasuryIns == 1 &&
              length spendOuts == 1 &&
              mintVal == lovelaceValueOf 0 &&
              elem nftOut continuingOutputs

        -- The script UTxO must be updated on both fields by the amount. Minted tokens must go to the treasury.
        -- No Update or Spending may occur.
        checkScriptMintingUse :: Proposal -> Bool
        checkScriptMintingUse p =
          let
              treasuryIns = [tx | tx <- txIns, ((txOutAddress $ txInInfoResolved tx) == treasury)]
              nftOuts = [tx | tx <- txOuts, (assetClassValueOf (txOutValue tx) nft > 0)]
              mintVal = txInfoMint txInfo
              nftOut = nftOuts !! 0
              continuingWithMint = [tx | tx <- txOuts, ((txOutValue tx) == mintVal && (txOutAddress tx) == treasury)]
          in
              length treasuryIns == 0 &&
              elem nftOut continuingOutputs &&
              length continuingWithMint == 1

        -- The NFT must go to the specified address
        -- The Treasury cannot be spent from.
        -- No minting may occur.
        checkScriptUpdate :: Proposal -> Bool
        checkScriptUpdate p =
          let
              treasuryIns = [tx | tx <- txIns, ((txOutAddress $ txInInfoResolved tx) == treasury)]
              nftOuts = [tx | tx <- txOuts, (assetClassValueOf (txOutValue tx) nft > 0)]
              nftOut = nftOuts !! 0
              nftAddress = txOutAddress nftOut
          in
              length treasuryIns == 0 &&
              mintVal == lovelaceValueOf 0 &&
              nftAddress == scriptAddr p

        checkScriptOutputs' :: Proposal -> Bool
        checkScriptOutputs' p =
            if spend p then
                checkScriptTreasuryUse p
            else if mint p then
                checkScriptMintingUse p
            else
                checkScriptUpdate p
              
        -- This function validates the spending from the DAO Treasury
        -- This function validates the minting to the DAO Treasury
        -- This function validates the spending of the DAO NFT.
        correctScriptOutputs :: Bool
        correctScriptOutputs =
          let
              propIn = proposalDatum $ propTxos !! 0
          in
              if (length propTxos) /= 1 then False else
                  case propIn of
                      Just p  ->
                          checkOnePath &&
                          checkScriptOutputs' p
                      Nothing -> False

-- We need this because we are returning a Boolean above.
data Voting
instance Scripts.ValidatorTypes Voting where
    type instance DatumType Voting = Proposal | Owner | TokenTrace | IdMaker
    type instance RedeemerType Voting = BuiltinData

-- This section allows for the code above to be easily compiled to the information necessary to deploy on chain.
votingPassValidatorInstance :: AssetClass -> Scripts.TypedValidator Voting
votingPassValidatorInstance asset = Scripts.mkTypedValidator @Voting
    ($$(PlutusTx.compile [||  votingPassValidator ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode asset)
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @Voting @Voting

votingPassValidatorHash :: AssetClass -> ValidatorHash
votingPassValidatorHash = Scripts.validatorHash . votingPassValidatorInstance

votingPassValidatorScript :: AssetClass -> TypedValidator
votingPassValidatorScript = Scripts.validatorScript . votingPassValidatorInstance

votingPassScriptAddress :: AssetClass -> Address
votingPassScriptAddress = Ledger.scriptAddress . votingPassValidatorScript

-- This section manages the Governance Token. Should this section change a reissuance of gov tokens is required.
{-# INLINABLE mkPolicy #-} -- AssetClass used as input should be the DAO's NFT. The script manages the treasury through spending of the NFT.
mkPolicy :: AssetClass -> BuiltinData -> ScriptContext -> Bool
mkPolicy asset _ ctx = traceIfFalse "The DAO's NFT is not present." (nftSum > 0)
  where
    txInfo = scriptContextTxInfo ctx
    txInValues = [txOutValue $ txInInfoResolved txIn | txIn <- txInfoInputs $ scriptContextTxInfo ctx]
    nftValues = [assetClassValueOf val asset | val <- txInValues]
    nftSum = sum nftValues

policy :: AssetClass -> Scripts.MintingPolicy
policy asset = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| Scripts.wrapMintingPolicy . mkPolicy ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode asset

curSymbol :: AssetClass -> CurrencySymbol
curSymbol asset = scriptCurrencySymbol $ policy asset