pragma solidity ^0.5.8;

contract RegistryHarness {
  
	string constant ATTESTATIONS_REGISTRY_ID = "Attestations";
	string constant BONDED_DEPOSITS_REGISTRY_ID = "BondedDeposits";
	string constant GAS_CURRENCY_WHITELIST_REGISTRY_ID = "GasCurrencyWhitelist";
	string constant GOLD_TOKEN_REGISTRY_ID = "GoldToken";
	string constant GOVERNANCE_REGISTRY_ID = "Governance";
	string constant RESERVE_REGISTRY_ID = "Reserve";
	string constant RANDOM_REGISTRY_ID = "Random";
	string constant SORTED_ORACLES_REGISTRY_ID = "SortedOracles";
	string constant VALIDATORS_REGISTRY_ID = "Validators";

	uint256 constant iamValidators = 1;
	uint256 constant iamGoldToken = 2;
	uint256 constant iamGovernance = 3;
	uint256 constant iamBondedDeposits = 4;
	
	uint256 constant iamSpartacus = 10000000;
	
	uint256 whoami;
	
	function getAddressFor(string calldata identifier) external returns (address) {
		if (bytes(identifier)[0] == 'V' && bytes(identifier)[1] == 'a') {
			whoami = iamValidators;
		} else if (bytes(identifier)[0] == 'G' && bytes(identifier)[1] == 'o' && bytes(identifier)[2] == 'l') {
			whoami = iamGoldToken;
		} else if (bytes(identifier)[0] == 'G' && bytes(identifier)[1] == 'o' && bytes(identifier)[2] == 'v') {
			whoami = iamGovernance;
		} else if (bytes(identifier)[0] == 'B') {
			whoami = iamBondedDeposits;
		} else {
			whoami = iamSpartacus; // random! irrelevant!
		}
		
		// Need to statically reason that registry always returns itself now. In particular if can call state-modifying code through the registry (goldToken?).
		return address(this);
	}


	// local fields from other contracts are prefixed with contract name, like this: contractName_fieldName
	mapping (address => bool) validators_validating;
	mapping (address => bool) governance_isVoting;
	mapping (address => bool) validators_isVoting;
	
	uint256 bondedDeposits_totalWeight;
	
	uint256 randomIndex;
	mapping (uint => bool) randomBoolMap;
	mapping (uint => uint256) randomUInt256Map;
	
	
	function isValidating(address account) external view returns (bool) {
		if (whoami == iamValidators) {
			return validators_validating[account];
		}
		
	}
	
	function isVoting(address x) external returns (bool) {
		if (whoami == iamValidators) {
			return validators_isVoting[x];
		} else if (whoami == iamGovernance) {
			return governance_isVoting[x];
		} else {
			return getRandomBool();
		}
	}
	
	function getTotalWeight() public returns (uint256) {
		if (whoami == iamBondedDeposits) {
			return bondedDeposits_totalWeight;
		} else {
			return getRandomUInt256();
		}
	}
	
	function getRandomBool() public returns (bool) {
		randomIndex++;
		return randomBoolMap[randomIndex];
	}
	
	function getRandomUInt256() public returns (uint256) {
		randomIndex++;
		return randomUInt256Map[randomIndex];
	}
	
	// TODO: For gold token - spartacus behavior should include wrecking havoc on balances.
}
