// SPDX-License-Identifier: MIT
pragma solidity =0.6.12;

import "./SolarPairFlatten.sol";

import "hardhat/console.sol";

contract CalHash {
    function getInitHash() public pure returns (bytes32) {
        bytes memory bytecode = type(SolarPair).creationCode;
        return keccak256(abi.encodePacked(bytecode));
    }
}
