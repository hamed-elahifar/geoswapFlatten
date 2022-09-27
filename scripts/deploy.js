// -------------------- بسم الله الرحمن الرحيم -------------------- //
console.clear();
const path = require("path");
const configFile = path.resolve(process.cwd(), `.env.${process.env.NODE_ENV}`);
require("dotenv").config({ path: configFile });

const { ethers } = require("hardhat");
const fs = require("fs");

let deployerAddress;
let factory;
let DistributorV2;
let pairs = [];

const trustedForwarder = process.env.TRUSTED_FORWARDER;

const sleepDuration = 10000;
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

const deployer = async (path, name = path, ...args) => {
  const Contract = await ethers.getContractFactory(path);
  const contract = await Contract.deploy(...args);
  await contract.deployed();

  console.log(`${name} address is: ${contract.address}`);
  console.log();

  const data = {
    address: contract.address,
    abi: JSON.parse(contract.interface.format("json")),
  };

  fs.writeFileSync(`abi/${name}.json`, JSON.stringify(data, null, 2));

  return { ...contract, abi: JSON.parse(contract.interface.format("json")) };
};

const approve = async (ERC20Contract, routerAddress) => {
  const totalSupply = await ERC20Contract.totalSupply();

  const receipt = await ERC20Contract.approve(routerAddress, totalSupply);
  await receipt.wait();

  const allowance = await ERC20Contract.allowance(
    deployerAddress,
    routerAddress
  );
  console.log(`${await ERC20Contract.name()} allowance: ${allowance}`);

  console.log(`Tx successful with hash: ${receipt.hash}`);
  console.log();
};

const createPair = async (tokenA, tokenB) => {
  const receipt = await factory.createPair(tokenA.address, tokenB.address, {
    // gasPrice: ethers.utils.parseUnits("10", "gwei"),
    // gasLimit: 1_000_000,
    // from: ownerAddress,
  });
  await receipt.wait();

  console.log(`Create Pair Tx Hash: ${receipt.hash}`);
  console.log();
};

const addLiquidity = async (tokenA, tokenB, amount) => {
  const receipt = await router.addLiquidity(
    tokenA.address, // address tokenA,
    tokenB.address, // address tokenB,
    100_000n, // uint256 amountADesired,
    100_000n, // uint256 amountBDesired,
    100n, // uint256 amountAMin,
    100n, // uint256 amountBMin,
    deployerAddress, // address to,
    Math.floor(Date.now() / 1000) + 60 * 10, // uint256 deadline
    {
      // gasPrice: ethers.utils.parseUnits("10", "gwei"),
      // gasLimit: 1_000_000,
      // from: ownerAddress,
    }
  );
  await receipt.wait();

  console.log(`Tx successful with hash: ${receipt.hash}`);
};

const startFarming = async () => {
  const receipt = await DistributorV2.startFarming();
  await receipt.wait();

  console.log(`Farming Started... ${receipt.hash}`);
  console.log();
};

const addPool = async (pair) => {
  const receipt = await DistributorV2.add(
    100, // uint256 _allocPoint,
    pair, // IBoringERC20 _lpToken,
    0, // uint16 _depositFeeBP,
    0, // uint256 _harvestInterval
    [trustedForwarder] // IComplexRewarder[] calldata _rewarders
  );
  await receipt.wait();

  console.log(`Tx successful with hash: ${receipt.hash}`);
};

const main = async () => {
  const [admin] = await ethers.getSigners();

  deployerAddress = admin.address;
  console.log(`Deploying contracts using ${deployerAddress}`);
  console.log();

  // Token
  const weth = await deployer("WETH");
  const a = await deployer("A");
  const b = await deployer("B");
  const c = await deployer("C");
  const dai = await deployer("DAI");
  const usdc = await deployer("USDC");
  const usdt = await deployer("USDT");
  const solarBeamToken = await deployer(
    "contracts/SolarBeamTokenFlatten.sol:SolarBeamToken",
    "SolarBeamToken",
    trustedForwarder
  );

  // Deploy Factory
  factory = await deployer(
    "contracts/SolarFactoryFlatten.sol:SolarFactory",
    "factory",
    deployerAddress
  );

  // Deploy Router
  const router = await deployer(
    "contracts/SolarRouter02Flatten.sol:SolarRouter02",
    "router",
    factory.address,
    weth.address
  );

  // Deploy multicall2
  await deployer("contracts/MulticallFlatten.sol:Multicall2", "Multicall2");

  // tokens Approve
  await approve(a, router.address);
  await approve(b, router.address);
  await approve(c, router.address);
  await approve(dai, router.address);
  await approve(usdc, router.address);
  await approve(usdt, router.address);

  // Create Pairs
  await createPair(dai, usdc);
  await createPair(usdt, usdc);
  await createPair(dai, usdt);

  const factoryPairsLength = await factory.allPairsLength();
  console.log("factoryPairsLength", factoryPairsLength);
  console.log();

  for (let i = 0; i < factoryPairsLength; i++) {
    const result = await factory.allPairs(i);
    console.log(`Pairs[${i}]: ${result}`);
    pairs.push(result);
  }

  // Deploy Farms
  DistributorV2 = await deployer(
    "contracts/SolarDistributorV2Flatten.sol:SolarDistributorV2",
    "SolarDistributorV2",
    solarBeamToken.address, // geos.address,
    100, // geosPerSec,
    deployerAddress, // dev.address,
    deployerAddress, // treasury.address,
    deployerAddress, // investor.address,
    200, // devPercent,
    200, // treasuryPercent,
    100 // investorPercent);
  );

  await startFarming();

  // get PairsInfo
  const farmPoolLength = await DistributorV2.poolLength();
  console.log("farmPoolLength", farmPoolLength);

  // Add Pool
  for (const pair of pairs) {
    await addPool(pair);
  }
};

main()
  .then(() => {
    process.exit(0);
  })
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });
