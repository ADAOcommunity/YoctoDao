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

{-# INLINABLE votingPassValidator #-}
votingPassValidator :: AssetClass -> BuiltinData -> BuiltinData -> ScriptContext -> Bool
votingPassValidator asset _ _ ctx =
  let
      txInfo = scriptContextTxInfo ctx

      -- We map over all of the inputs to the transaction to gather the number of votes present.
      txInValues = [txOutValue $ txInInfoResolved txIn | txIn <- txInfoInputs $ scriptContextTxInfo ctx]
      tokenValues = [assetClassValueOf val asset | val <- txInValues]
      votes = sum tokenValues -- sum the occurrences of the tokenClass inside of txInValues
  in
      traceIfFalse "Not enough votes" (votes > 5)

-- We need this because we are returning a Boolean above.
data Voting
instance Scripts.ValidatorTypes Voting where
    type instance DatumType Voting = BuiltinData
    type instance RedeemerType Voting = BuiltinData


-- This section allows for the code above to be easily compiled to the information necessary to deploy on chain.
votingPassValidatorInstance :: AssetClass -> Scripts.TypedValidator Voting
votingPassValidatorInstance asset = Scripts.mkTypedValidator @Voting
    ($$(PlutusTx.compile [||  votingPassValidator ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode asset)
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @BuiltinData @BuiltinData

votingPassValidatorHash :: AssetClass -> ValidatorHash
votingPassValidatorHash = Scripts.validatorHash . votingPassValidatorInstance

votingPassValidatorScript :: AssetClass -> Validator
votingPassValidatorScript = Scripts.validatorScript . votingPassValidatorInstance

votingPassScriptAddress :: AssetClass -> Address
votingPassScriptAddress = Ledger.scriptAddress . votingPassValidatorScript

-- This section manages the Governance Token. Should this section change a reissuance of gov tokens is required.
{-# INLINABLE mkPolicy #-}
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