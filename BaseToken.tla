---------------------------- MODULE BaseToken ----------------------------

EXTENDS Integers, Apalache, FiniteSets

\* @typeAlias: limit = { min: Int, max: Int };
\* @typeAlias: feeRecord = { currency: Str, rate: Int, floor: Int, cap: Int };
BaseTokenTypeAliases == TRUE

CONSTANTS
    \* @type: Set(Str);
    Addresses,          \* Set of user addresses
    \* @type: Set(Str);
    Currencies,         \* Set of currencies (except this token)
    \* @type: Int;
    MaxAmount,          \* Max amount for the operations
    \* @type: Str;
    Issuer,             \* Issuer address
    \* @type: Str;
    FeeSetter,          \* Address setting fee value
    \* @type: Str;
    FeeAddressSetter,   \* Address setting addr for receiving fees
    \* @type: Str;
    FeeAddress          \* Address receiving fees

VARIABLES
    \* @type: Str -> Int;
    tokenBalances,
    \* @type: <<Str, Str>> -> Int;
    allowedBalances,    \* [address: Address, currency: Currency] -> Nat
    \* @type: Int;
    totalEmission,
    \* @type: <<Str, Str>> -> Int;
    rates,              \* [dealType: String, currency: Currency] -> Rate
    \* @type: <<Str, Str>> -> $limit;
    limits,             \* [dealType: String, currency: Currency] -> [min: Nat, max: Nat]
    \* @type: $feeRecord;
    fee,                \* [currency: String, rate: Nat, floor: Nat, cap: Nat]
    \* @type: Str;
    feeAddress

vars == <<tokenBalances, allowedBalances, totalEmission, rates, limits,
          fee, feeAddress>>

DealTypes == {"buyToken", "buyBack"}

Init ==
    /\ tokenBalances = [a \in Addresses |-> 0]
    \* Initialize allowed balances for non-issuer, non-fee addresses
    /\ allowedBalances = [ac \in Addresses \X Currencies |->
            IF ac[1] # Issuer /\ ac[1] # FeeAddress THEN MaxAmount ELSE 0]
    /\ totalEmission = 0
    /\ rates = [dc \in DealTypes \X Currencies |-> 0]
    /\ limits = [dc \in DealTypes \X Currencies |-> [min |-> 0, max |-> 0]]
    /\ fee = [currency |-> "TOKEN", rate |-> 0, floor |-> 0, cap |-> 0]
    /\ feeAddress = FeeAddress

--------------------------------------------------------------------------------
\* Helper functions
--------------------------------------------------------------------------------

AddBalance(sum, addr) == sum + tokenBalances[addr]

\* Sum of all token balances
TotalTokenBalance == ApaFoldSet(AddBalance, 0, Addresses)

\* Limit check
InLimits(amount, dealType, currency) ==
    LET lim == limits[<<dealType, currency>>]
    IN /\ amount >= lim.min
       /\ (lim.max = 0 \/ amount <= lim.max)

\* calcFee from transfer.go
CalcTransferFee(amount, sender, recipient) ==
    IF sender = recipient THEN
        \* No fee for self-transfers
        0
    ELSE IF fee.rate = 0 THEN
        0
    ELSE
        \* Base fee: amount * fee.rate
        LET baseFee == amount * fee.rate
            \* Apply rate if fee currency is not TOKEN
            feeWithRate == IF fee.currency # "TOKEN" THEN
                              \* baseFee * rate
                              baseFee * rates[<<"buyToken", fee.currency>>]
                           ELSE
                              baseFee
            \* Apply floor
            withFloor == IF feeWithRate < fee.floor 
                         THEN fee.floor 
                         ELSE feeWithRate
            \* Apply cap
            finalFee == IF fee.cap > 0 /\ withFloor > fee.cap 
                        THEN fee.cap 
                        ELSE withFloor
        IN finalFee

\* CalcPrice from limit.go
CalcPrice(amount, dealType, currency) ==
    IF rates[<<dealType, currency>>] > 0 THEN
        amount * rates[<<dealType, currency>>] \* price = (amount * rate)
    ELSE
        0

--------------------------------------------------------------------------------

\* TxTransfer from transfer.go
Transfer(sender, recipient, amount) ==
    /\ sender # recipient
    /\ amount > 0
    /\ amount <= tokenBalances[sender]
    /\ LET feeAmount == CalcTransferFee(amount, sender, recipient)
       IN IF fee.currency = "TOKEN" THEN
              \* Fee in TOKEN
              /\ feeAmount <= tokenBalances[sender] - amount
              /\ IF sender = feeAddress THEN
                     \* operations.go:95-109
                     \* sender == feeAddress, merge operations
                     /\ tokenBalances' = [tokenBalances EXCEPT
                           ![sender] = @ - amount,
                           ![recipient] = @ + amount]
                     /\ UNCHANGED allowedBalances
                 ELSE IF recipient = feeAddress THEN
                     \* recipient == feeAddress, merge operations
                     /\ tokenBalances' = [tokenBalances EXCEPT
                           ![sender] = @ - amount - feeAmount,
                           ![recipient] = @ + amount + feeAmount]
                     /\ UNCHANGED allowedBalances
                 ELSE
                     \* Standard case: all addresses differ
                     /\ tokenBalances' = [tokenBalances EXCEPT
                           ![sender] = @ - amount - feeAmount,
                           ![recipient] = @ + amount,
                           ![feeAddress] = @ + feeAmount]
                     /\ UNCHANGED allowedBalances
          ELSE
              \* Fee in allowed currency
              /\ feeAmount <= allowedBalances[<<sender, fee.currency>>]
              /\ tokenBalances' = [tokenBalances EXCEPT
                    ![sender] = @ - amount,
                    ![recipient] = @ + amount]
              /\ IF sender = feeAddress THEN
                     \* operations.go:95-109
                     \* sender == feeAddress in allowed currency, merge
                     allowedBalances' = [allowedBalances EXCEPT
                           ![<<feeAddress, fee.currency>>] = @ - feeAmount + feeAmount]
                 ELSE IF recipient = feeAddress THEN
                     \* recipient == feeAddress in allowed currency
                     allowedBalances' = [allowedBalances EXCEPT
                           ![<<sender, fee.currency>>] = @ - feeAmount,
                           ![<<feeAddress, fee.currency>>] = @ + feeAmount]
                 ELSE
                     \* Standard case
                     allowedBalances' = [allowedBalances EXCEPT
                           ![<<sender, fee.currency>>] = @ - feeAmount,
                           ![<<feeAddress, fee.currency>>] = @ + feeAmount]
    /\ UNCHANGED <<totalEmission, rates, limits, fee, feeAddress>>

\* func (bt *BaseToken) TxBuyToken(sender *types.Sender, amount *big.Int, currency string) error
\* (buy_buyback.go, 26-45)
BuyToken(buyer, amount, currency) ==
    /\ buyer # Issuer
    /\ amount > 0
    /\ rates[<<"buyToken", currency>>] > 0
    /\ InLimits(amount, "buyToken", currency)
    /\ amount <= tokenBalances[Issuer]  \* Issuer has enough token balance
    /\ LET price == CalcPrice(amount, "buyToken", currency)
       IN /\ price <= allowedBalances[<<buyer, currency>>]  \* Buyer has enough balance
          /\ tokenBalances' = [tokenBalances EXCEPT
                ![Issuer] = @ - amount,
                ![buyer] = @ + amount]
          /\ allowedBalances' = [allowedBalances EXCEPT
                ![<<buyer, currency>>] = @ - price,
                ![<<Issuer, currency>>] = @ + price]
    /\ UNCHANGED <<totalEmission, rates, limits, fee, feeAddress>>

\* func (bt *BaseToken) TxBuyBack(sender *types.Sender, amount *big.Int, currency string) error
\* (buy_buyback.go, 48-67)
BuyBack(seller, amount, currency) ==
    /\ seller # Issuer
    /\ amount > 0
    /\ rates[<<"buyBack", currency>>] > 0
    /\ InLimits(amount, "buyBack", currency)
    /\ amount <= tokenBalances[seller]  \* Seller has enough token balance
    /\ LET price == CalcPrice(amount, "buyBack", currency)
       IN /\ price <= allowedBalances[<<Issuer, currency>>] \* Issuer has enough balance
          /\ tokenBalances' = [tokenBalances EXCEPT
                ![seller] = @ - amount,
                ![Issuer] = @ + amount]
          /\ allowedBalances' = [allowedBalances EXCEPT
                ![<<Issuer, currency>>] = @ - price,
                ![<<seller, currency>>] = @ + price]
    /\ UNCHANGED <<totalEmission, rates, limits, fee, feeAddress>>

\* func (bt *BaseToken) EmissionAdd(amount *big.Int) error
\* (token.go, 108-119 lines)
EmissionAdd(actor, amount) ==
    /\ actor = Issuer \* only Issuer can change emission (from higher level)
    /\ amount > 0
    \* Issuer mints to itself
    /\ tokenBalances' = [tokenBalances EXCEPT ![Issuer] = @ + amount]
    /\ totalEmission' = totalEmission + amount
    /\ UNCHANGED <<allowedBalances, rates, limits, fee, feeAddress>>

\* func (bt *BaseToken) EmissionSub(amount *big.Int) error
\* (token.go, 122-135 lines)
EmissionSub(actor, amount) ==
    /\ actor = Issuer \* only Issuer can change emission (from higher level)
    /\ amount > 0
    /\ amount <= totalEmission
    \* Issuer burns its tokens
    /\ amount <= tokenBalances[Issuer]
    /\ tokenBalances' = [tokenBalances EXCEPT ![Issuer] = @ - amount]
    /\ totalEmission' = totalEmission - amount
    /\ UNCHANGED <<allowedBalances, rates, limits, fee, feeAddress>>

\* func (bt *BaseToken) TxSetRate(sender *types.Sender, dealType string, currency string, rate *big.Int) error
\* (methods.go, 168-197 lines)
SetRate(actor, dealType, currency, rate) ==
    /\ actor = Issuer
    /\ dealType \in DealTypes
    /\ currency \in Currencies
    /\ rate > 0
    /\ rates' = [rates EXCEPT ![<<dealType, currency>>] = rate]
    /\ UNCHANGED <<tokenBalances, allowedBalances, totalEmission, limits, fee, feeAddress>>

\* func (bt *BaseToken) TxSetLimits(sender *types.Sender, dealType string, currency string, min *big.Int, max *big.Int) error
\* (methods.go, 200-226 lines)
SetLimits(actor, dealType, currency, minLimit, maxLimit) ==
    /\ actor = Issuer
    /\ dealType \in DealTypes
    /\ currency \in Currencies
    /\ minLimit >= 0
    /\ maxLimit >= 0
    /\ (maxLimit = 0 \/ minLimit <= maxLimit)
    /\ rates[<<dealType, currency>>] > 0  \* Rate must be set
    /\ limits' = [limits EXCEPT 
            ![<<dealType, currency>>] = [min |-> minLimit, max |-> maxLimit]]
    /\ UNCHANGED <<tokenBalances, allowedBalances, totalEmission, rates, fee, feeAddress>>

\* func (bt *BaseToken) TxDeleteRate(sender *types.Sender, dealType string, currency string) error
\* (methods.go, 228-248 lines)
DeleteRate(actor, dealType, currency) ==
    /\ actor = Issuer
    /\ dealType \in DealTypes
    /\ currency \in Currencies
    /\ rates' = [rates EXCEPT ![<<dealType, currency>>] = 0]
    \* Original code clears Rates, including limits:
    /\ limits' = [limits EXCEPT ![<<dealType, currency>>] = [min |-> 0, max |-> 0]]
    /\ UNCHANGED <<tokenBalances, allowedBalances, totalEmission, fee, feeAddress>>

\* func (bt *BaseToken) TxSetFee(sender *types.Sender, currency string, fee *big.Int, floor *big.Int, cap *big.Int) error
\* (transfer.go, 178-196 lines)
SetFee(actor, currency, feeRate, floor, cap) ==
    /\ actor = FeeSetter
    /\ currency \in (Currencies \union {"TOKEN"})
    /\ feeRate >= 0 /\ feeRate <= 1
    /\ floor >= 0
    /\ cap >= 0
    /\ (cap = 0 \/ floor <= cap)
    /\ fee' = [currency |-> currency, rate |-> feeRate, floor |-> floor, cap |-> cap]
    /\ UNCHANGED <<tokenBalances, allowedBalances, totalEmission, rates, limits, feeAddress>>

\* func (bt *BaseToken) TxSetFeeAddress(sender *types.Sender, address *types.Address) error
\* (transfer.go, 199-210 lines)
SetFeeAddress(actor, newAddress) ==
    /\ actor = FeeAddressSetter
    /\ newAddress \in Addresses
    /\ feeAddress' = newAddress
    /\ UNCHANGED <<tokenBalances, allowedBalances, totalEmission, rates, limits, fee>>

--------------------------------------------------------------------------------

Next ==
    \/ \E sender, recipient \in Addresses, amount \in 1..MaxAmount:
        Transfer(sender, recipient, amount)
    \/ \E buyer \in Addresses, amount \in 1..MaxAmount, currency \in Currencies:
        BuyToken(buyer, amount, currency)
    \/ \E seller \in Addresses, amount \in 1..MaxAmount, currency \in Currencies:
        BuyBack(seller, amount, currency)
    \/ \E amount \in 1..MaxAmount:
        EmissionAdd(Issuer, amount)
    \/ \E amount \in 1..MaxAmount:
        EmissionSub(Issuer, amount)
    \/ \E dealType \in DealTypes, currency \in Currencies, rate \in 1..2:
        SetRate(Issuer, dealType, currency, rate)
    \/ \E dealType \in DealTypes, currency \in Currencies,
          minLimit \in 0..1, maxLimit \in 0..MaxAmount:
        SetLimits(Issuer, dealType, currency, minLimit, maxLimit)
    \/ \E dealType \in DealTypes, currency \in Currencies:
        DeleteRate(Issuer, dealType, currency)
    \/ \E currency \in (Currencies \union {"TOKEN"}),
          feeRate \in 0..2, floor \in 0..1, cap \in 0..MaxAmount:
        SetFee(FeeSetter, currency, feeRate, floor, cap)
    \/ \E newAddress \in Addresses:
        SetFeeAddress(FeeAddressSetter, newAddress)

Spec == Init /\ [][Next]_vars

--------------------------------------------------------------------------------
\* INVARIANTS
--------------------------------------------------------------------------------

TypeInvariant ==
    /\ tokenBalances \in [Addresses -> Nat]
    /\ allowedBalances \in [Addresses \X Currencies -> Nat]
    /\ totalEmission \in Nat
    /\ rates \in [DealTypes \X Currencies -> Nat]
    /\ limits \in [DealTypes \X Currencies -> [min: Nat, max: Nat]]
    /\ fee.currency \in (Currencies \union {"TOKEN"})
    /\ fee.rate \in Nat
    /\ fee.floor \in Nat
    /\ fee.cap \in Nat
    /\ feeAddress \in Addresses

\* INVARIANT 0: Balances are non-negative
BalancesNonNegative ==
    /\ \A a \in Addresses: tokenBalances[a] >= 0
    /\ \A a \in Addresses, c \in Currencies: allowedBalances[<<a, c>>] >= 0

\* INVARIANT 1: Total token balance equals total emission
TotalBalanceEqualsEmission ==
    TotalTokenBalance = totalEmission

\* INVARIANT 2: Emission is non-negative
EmissionNonNegative ==
    totalEmission >= 0

\* INVARIANT 3: Fee bounds are valid
FeeRateValid ==
    /\ fee.rate >= 0
    /\ fee.floor >= 0
    /\ fee.cap >= 0
    /\ (fee.cap = 0 \/ fee.floor <= fee.cap)

\* INVARIANT 4: Limits are valid
LimitsValid ==
    \A dt \in DealTypes, c \in Currencies:
        LET lim == limits[<<dt, c>>]
        IN lim.max = 0 \/ lim.min <= lim.max

\* INVARIANT 5: Rates are non-negative
RatesNonNegative ==
    \A dt \in DealTypes, c \in Currencies:
        rates[<<dt, c>>] >= 0

\* ACTION INVARIANT 0: Only issuer changes emission
\* If totalEmission changed, it was EmissionAdd/EmissionSub
EmissionAuthorization ==
    totalEmission' # totalEmission =>
        \* Issuer balance changes by the same amount
        tokenBalances'[Issuer] - tokenBalances[Issuer] = totalEmission' - totalEmission

\* ACTION INVARIANT 1: BuyToken consistency
\* If token balance increases and allowed decreases, 
\* it is a buy at a set rate within limits
BuyConsistency ==
    \A a \in Addresses, c \in Currencies:
        (a # Issuer
         /\ allowedBalances'[<<a, c>>] < allowedBalances[<<a, c>>]
         /\ tokenBalances'[a] > tokenBalances[a]) =>
    /\ InLimits(tokenBalances'[a] - tokenBalances[a], "buyToken", c)
    /\ rates[<<"buyToken", c>>] > 0
    /\ allowedBalances[<<a, c>>] - allowedBalances'[<<a, c>>] =
        (tokenBalances'[a] - tokenBalances[a]) * rates[<<"buyToken", c>>]

\* ACTION INVARIANT 2: BuyBack consistency
BuyBackConsistency ==
    \A a \in Addresses, c \in Currencies:
        (a # Issuer
         /\ allowedBalances'[<<a, c>>] > allowedBalances[<<a, c>>]
         /\ tokenBalances[a] > tokenBalances'[a]) =>
    /\ InLimits(tokenBalances[a] - tokenBalances'[a], "buyBack", c)
    /\ rates[<<"buyBack", c>>] > 0
    /\ allowedBalances'[<<a, c>>] - allowedBalances[<<a, c>>] =
        (tokenBalances[a] - tokenBalances'[a]) * rates[<<"buyBack", c>>]

\* ACTION INVARIANT 3: Transfer consistency with fees
\* Fee can be in TOKEN or allowed currency; special cases for feeAddress
TransferConsistency ==
    \A sender, recipient \in Addresses:
        \* Transfer-like pattern:
        \* - no changes to rates or emission
        \* - sender sends tokens, recipient receives
        \* - recipient allowed balances unchanged (exclude BuyToken/BuyBack)
        (totalEmission' = totalEmission
         /\ rates' = rates
         /\ sender # recipient
         /\ tokenBalances[sender] > tokenBalances'[sender]
         /\ tokenBalances'[recipient] > tokenBalances[recipient]
         /\ \A c \in Currencies: allowedBalances'[<<recipient, c>>] = allowedBalances[<<recipient, c>>]) =>
        LET
            \* Tokens sent (sender balance delta)
            sentTokens == tokenBalances[sender] - tokenBalances'[sender]
            \* Tokens received by recipient
            receivedTokens == tokenBalances'[recipient] - tokenBalances[recipient]
            \* feeAddress token delta
            feeTokens == tokenBalances'[feeAddress] - tokenBalances[feeAddress]
            \* Any sender allowed balance decrease
            senderAllowedChanged == \E c \in Currencies:
                allowedBalances[<<sender, c>>] > allowedBalances'[<<sender, c>>]
            \* Any feeAddress allowed balance increase
            feeAllowedIncrease == \E c \in Currencies:
                allowedBalances'[<<feeAddress, c>>] > allowedBalances[<<feeAddress, c>>]
        IN
        \* Two main cases
        \/ \* Case 1: Fee in TOKEN or no fee
           \* Only token balances change
           /\ ~senderAllowedChanged
           /\ IF sender = feeAddress THEN
                  \* sender = feeAddress: no fee charged to sender
                  \* recipient still receives amount
                  /\ sentTokens = receivedTokens
                  /\ (~feeAllowedIncrease)
              ELSE IF recipient = feeAddress THEN
                  \* recipient = feeAddress: receives amount + fee (if fee > 0)
                  /\ sentTokens >= receivedTokens
                  /\ (~feeAllowedIncrease)
                  \* receivedTokens = amount + feeAmount
                  \* sentTokens = amount + feeAmount
              ELSE
                  \* Standard case: sender pays amount + fee
                  /\ sentTokens >= receivedTokens
                  /\ feeTokens >= 0
                  /\ sentTokens = receivedTokens + feeTokens
        \/ \* Case 2: Fee in allowed currency
           \* Tokens transfer 1:1, fee charged from allowed
           /\ sentTokens = receivedTokens
           /\ feeTokens = 0
           /\ IF sender = feeAddress THEN
                  \* sender = feeAddress: no fee charged or credited
                  /\ ~senderAllowedChanged
                  /\ ~feeAllowedIncrease
              ELSE IF recipient = feeAddress THEN
                  \* recipient = feeAddress: fee debited then credited
                  /\ senderAllowedChanged => feeAllowedIncrease
                  /\ \A c \in Currencies:
                       allowedBalances[<<sender, c>>] - allowedBalances'[<<sender, c>>] =
                       allowedBalances'[<<feeAddress, c>>] - allowedBalances[<<feeAddress, c>>]
              ELSE
                  \* Standard case: sender pays fee in allowed
                  /\ senderAllowedChanged
                  /\ feeAllowedIncrease
                  /\ \A c \in Currencies:
                       \* If fee charged in currency c
                       (allowedBalances[<<sender, c>>] > allowedBalances'[<<sender, c>>]) =>
                       \* feeAddress receives the same amount
                       (allowedBalances[<<sender, c>>] - allowedBalances'[<<sender, c>>] =
                        allowedBalances'[<<feeAddress, c>>] - allowedBalances[<<feeAddress, c>>])

SafetyInvariant ==
    /\ TypeInvariant
    /\ BalancesNonNegative
    /\ EmissionNonNegative
    /\ FeeRateValid
    /\ LimitsValid
    /\ RatesNonNegative

ActionSafetyInvariant ==
    /\ EmissionAuthorization
    /\ BuyConsistency
    /\ BuyBackConsistency
    /\ TransferConsistency

================================================================================
