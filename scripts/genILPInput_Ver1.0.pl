#! /usr/bin/perl

use strict 'vars';
use strict 'refs';
use strict 'subs';

use POSIX;

use Cwd;

### Revision History : Ver 1.0 #####
# 2019-11-26 Initial Release
#
### Pre-processing ########################################################
my $ARGC        = @ARGV;
my $workdir     = getcwd();
my $outdir      = "$workdir/inputsILP";
my $infile      = "";

my $BoundaryCondition = 1; 
my $SON = 1;               
my $DoublePowerRail = 1;   
my $MAR_Parameter = 0;     # ARGV[1], 2: (Default), Integer
my $EOL_Parameter = 0;     # ARGV[2], 2: (Default), Integer
my $VR_Parameter = 0;      # ARGV[3], sqrt(2)=1.5 : (Default), Floating
my $PRL_Parameter = 0;     # ARGV[4], 1 : (Default). Integer
my $SHR_Parameter = 0;     # ARGV[5], 2 : (Default),  <2 -> No need to implement.

if ($ARGC != 6) {
    print "\n*** Error:: Wrong CMD";
    print "\n   [USAGE]: ./PL_FILE [inputfile_pinLayout] [MAR, 2(D)] [EOL, 2(D)] [VR, sqrt(2)(D)] [PRL, 1(D)], [SHR, 2(D)]\n\n";
    exit(-1);
} else {
    $infile             = $ARGV[0];
    $MAR_Parameter      = $ARGV[1];
    $EOL_Parameter      = $ARGV[2];
    $VR_Parameter       = $ARGV[3];
    $PRL_Parameter      = $ARGV[4];
    $SHR_Parameter      = $ARGV[5];

    if ($MAR_Parameter == 0){
        print "\n*** Disable MAR (When Parameter == 0) ***\n";
    }
    if ($EOL_Parameter == 0){
        print "\n*** Disable EOL (When Parameter == 0) ***\n";
    }     
    if ( $VR_Parameter == 0){
        print "\n*** Disable VR (When Parameter == 0) ***\n";
    }
    if ( $PRL_Parameter == 0){
        print "\n*** Disable PRL (When Parameter == 0) ***\n";
    }
    if ( $SHR_Parameter < 2){
        print "\n*** Disable SHR (When Parameter <= 1) ***\n";
    }
}

if (!-e "./$infile") {
    print "\n*** Error:: FILE DOES NOT EXIST..\n";
    print "***         $workdir/$infile\n\n";
    exit(-1);
} else {
    print "\n";
    print "a   Version Info : 1.0 Initial Release \n";

    print "a        Design Rule Parameters : [MAR = $MAR_Parameter , EOL = $EOL_Parameter, VR = $VR_Parameter, PRL = $PRL_Parameter, SHR = $SHR_Parameter]\n";

    print "a   Generating CPLEX inputfile based on the following files.\n";
    print "a     Input Layout:  $workdir/$infile\n";
}

### Output Directory Creation, please see the following reference:
system "mkdir -p $outdir";

my $outfile     = "$outdir/".(split /\./, (split /\//, $infile)[$#_])[0].".lp";
print "a     CPLEX File:    $outfile\n";

### Variable Declarations
my $width = 0;
my $placementRow = 0;
my $trackEachRow = 0;
my $numTrackH = 0;
my $numTrackV = 0;
my $numMetalLayer = 3;      # M0 includes super-sources and super-sinks, and normal M1, M2, M3.

### PIN variables
my @pins = ();
my @pin = ();
my $pinName = "";
my $pin_netID = ""; 
my $pin_stdID = "";			
my $pin_orgName = "";		
my $pinIO = "";
my $binRow = -1;
my $binCol = -1;
my $pinXpos = -1;
my @pinYpos = ();
my $pinLength = -1;
my $pinStart = -1;
my $totalPins = -1;
my %h_pins = ();

### NET variables
my @nets = ();
my @net = ();
my $netName = "";
my $netRName = "";
my $netID = -1;
my $N_pinNets = 0;
my $numSinks = -1;
my $source_ofNet = "";
my @pins_inNet = ();
my @sinks_inNet = ();
my $totalNets = -1;
my %h_nets = ();
my %h_nets_rname = ();
my %h_nets_id = ();
my $idx_nets = 0;

### Route Variables
my @metal = ();
my $no_vobs = 0;

my $infileStatus = "init";

### Read Inputfile and Build Data Structure
open (my $in, "./$infile");
while (<$in>) {
    my $line = $_;
    chomp($line);

    ### Status of Input File
    if ($line =~ /===BinInfo===/) {
        $infileStatus = "bin";
    } 
    elsif ($line =~ /===NetInfo===/) {
        $infileStatus = "net";
    }
    elsif ($line =~ /===PinInfo===/) {
        $infileStatus = "pin";
    }
    elsif ($line =~ /===RouteInfo===/) {
        $infileStatus = "route";
    }

    ### Infile Status: init
    if ($infileStatus eq "init") {
        if ($line =~ /Vertical Obstacle Width\s*= (\d+)/) {
            $no_vobs = $1;
        }
        elsif ($line =~ /Width of Routing Clip\s*= (\d+)/) {
            $width = $1;
			if($no_vobs > 0){
				$numTrackV = $width + 2*$no_vobs;
			}
			else{
				$numTrackV = $width + 2;
			}
            print "a     # Vertical Tracks   = $numTrackV\n";
        }
        elsif ($line =~ /Height of Routing Clip\s*= (\d+)/) {
            $placementRow = $1;
        }
        elsif ($line =~ /Tracks per Placement Row\s*= (\d+)/) {
            $trackEachRow = $1;
            $numTrackH = $placementRow * $trackEachRow + ($placementRow + 1);
            print "a     # Horizontal Tracks = $numTrackH\n";
        }
    }

    ### Infile Status: pin
    if ($infileStatus eq "pin") {
		# Additional Input Type Definition
        if ($line =~ /^i   pin(\d+)\s*(\S+)\s*(\w+)\s*(\S+)\s*(\S+)\s*(\S+)\s*(\S+)\s*(\S+)\s*(\S+)/) {			# (190104_ldy)
            $pinName = "pin".$1;
            $pin_netID = $2; 
			if($pin_netID eq "null"){
				next;
			}
            $pin_stdID = $3; 
            $pin_orgName = $4; 
            $pinIO = $5;
            $binCol = $6;
            $binRow = $7;
            $pinLength = $8;
            $pinStart = $9;
			if($no_vobs > 0){
				$pinXpos = $binCol + $no_vobs;
			}
			else{
				$pinXpos = $binCol + 1;
			}
			@pinYpos = ();
			for my $pinRow (1 .. $pinLength) {
				push (@pinYpos, ($trackEachRow + 1) * $binRow + $pinStart + $pinRow );
			}
			@pin = ($pinName, $pin_netID, $pinIO, $pinLength, $pinXpos, [@pinYpos]);
			push (@pins, [@pin]);
			$h_pins{$pinName} = [@pin];
        }
    }

    ### Infile Status: net
    if ($infileStatus eq "net") {
        if ($line =~  /^i   net(\S+)\s*(\S+)\s*(\d+)PinNet/) {
            @net = split /\s+/, $line;
            $netID = $1;
            $netName = "net".$netID;
            $netRName = $2;
            $N_pinNets = $3;
            @pins_inNet = ();
            for my $pinIndex_inNet (0 .. $N_pinNets-1) {
                push (@pins_inNet, $net[4 + $pinIndex_inNet]);
            }
            $source_ofNet = $pins_inNet[$N_pinNets-1];
            $numSinks = $N_pinNets - 1;
            @sinks_inNet = ();
            for my $sinkIndex_inNet (0 .. $numSinks-1) {
                push (@sinks_inNet, $net[4 + $sinkIndex_inNet]);
            }
            @net = ($netName, $netID, $N_pinNets, $source_ofNet, $numSinks, [@sinks_inNet], [@pins_inNet], $netRName);
            push (@nets, [@net]);
			$h_nets{$netName} = $idx_nets;
			$h_nets_rname{$netName} = $netRName;
			$h_nets_id{$netRName} = $netName;
			$idx_nets++;
		}
    }

	### Infile Status: route
	if ($infileStatus eq "route") {
		if ($line =~ /^i\s*([o_]*net\S+)\s*(\S+)\s*(\S+)\s*(\S+)\s*(\S+)\s*(\S+)\s*(\S+)/){
			my $net_name = $1;
			my $fromM = $2;
			my $toM = $3;
			my $fromR = $4;
			my $toR = $5;
			my $fromC = $6;
			my $toC = $7;
			push(@metal, [($net_name, $fromM, $toM, $fromR, $toR, $fromC, $toC)]);
		}
	}
}
close ($in);

$totalPins = scalar @pins;
$totalNets = scalar @nets;
print "a     # Pins              = $totalPins\n";
print "a     # Nets              = $totalNets\n";

my %h_obs_remove = ();
my %h_obs_extnode = ();
# Pre-processing for Obstacle
if(scalar(@metal)>0){
	for(my $i=0; $i<=$#metal; $i++){
		# obstacle metal - set bounds for metal variables
		if(!exists($h_nets_id{$metal[$i][0]})){
			my $vName1 = "";
			my $vName2 = "";
			if($no_vobs == 0){
				$vName1 = "m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+1);
				$vName2 = "m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+1);
			}
			else{
				$vName1 = "m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$no_vobs);
				$vName2 = "m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$no_vobs);
			}
			$h_obs_remove{"($vName1)($vName2)"} = 1;
		}
		else{
			my $offset = 0;
			if($no_vobs == 0){
				$offset = 1;
			}
			else{
				$offset = $no_vobs;
			}
			if($metal[$i][1] == $metal[$i][2] && $metal[$i][1]%2 == 0){
				if ($metal[$i][5] == -1){
					$h_obs_extnode{"m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset)} = 1;
				}
				elsif ($metal[$i][6] == $numTrackV - 2*$no_vobs){
					$h_obs_extnode{"m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset)} = 1;
				}
			}
			elsif($metal[$i][1] == $metal[$i][2] && $metal[$i][1]%2 == 1){
				if($metal[$i][3] == 0){
					$h_obs_extnode{"m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset)} = 1;
				}
				elsif($metal[$i][4] == $numTrackH - 1){
					$h_obs_extnode{"m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset)} = 1;
				}
			}
		}
	}
}

### VERTEX Generation
### VERTEX Variables
my %vertices = ();
my @vertex = ();
my $numVertices = -1;
my $vIndex = 0;
my $vName = "";
my @vADJ = ();
my $vL = "";
my $vR = "";
my $vF = "";
my $vB = "";
my $vU = "";
my $vD = "";
my $vFL = "";
my $vFR = "";
my $vBL = "";
my $vBR = "";

### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
for my $metal (1 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    for my $row (0 .. $numTrackH-1) {
        for my $col (0 .. $numTrackV-1) {
            $vName = "m".$metal."r".$row."c".$col;
			if ($col == 0) { ### Left Vertex
				$vL = "null";
			} 
			else {
				$vL = "m".$metal."r".$row."c".($col-1);
			}
			if ($col == $numTrackV-1) { ### Right Vertex
				$vR = "null";
			}
			else {
				$vR = "m".$metal."r".$row."c".($col+1);
			}
			if ($row == 0) { ### Front Vertex
				$vF = "null";
			}
			else {
				$vF = "m".$metal."r".($row-1)."c".$col;
			}
			if ($row == $numTrackH-1) { ### Back Vertex
				$vB = "null";
			}
			else {
				$vB = "m".$metal."r".($row+1)."c".$col;
			}
			if ($metal == $numMetalLayer) { ### Up Vertex
				$vU = "null";
			}
			else {
				$vU = "m".($metal+1)."r".$row."c".$col;
			}
			if ($metal == 1) { ### Down Vertex
				$vD = "null";
			}
			else {
				$vD = "m".($metal-1)."r".$row."c".$col;
			}
			if ($row == 0 || $col == 0) { ### FL Vertex
				$vFL = "null";
			}
			else {
				$vFL = "m".$metal."r".($row-1)."c".($col-1);
			}
			if ($row == 0 || $col == $numTrackV-1) { ### FR Vertex
				$vFR = "null";
			}
			else {
				$vFR = "m".$metal."r".($row-1)."c".($col+1);
			}
			if ($row == $numTrackH-1 || $col == 0) { ### BL Vertex
				$vBL = "null";
			}
			else {
				$vBL = "m".$metal."r".($row+1)."c".($col-1);
			}
			if ($row == $numTrackH-1 || $col == $numTrackV-1) { ### BR Vertex
				$vBR = "null";
			}
			else {
				$vBR = "m".$metal."r".($row+1)."c".($col+1);
			}

            @vADJ = ($vL, $vR, $vF, $vB, $vU, $vD, $vFL, $vFR, $vBL, $vBR);
            @vertex = ($vIndex, $vName, $metal, $row, $col, [@vADJ]);
            $vertices{$vName} = [@vertex];
            $vIndex++;
        }
    }
}
$numVertices = keys %vertices;
print "a     # Vertices          = $numVertices\n";

### DIRECTED EDGE Generation
### DIRECTED EDGE Variables
my @dEdges = ();
my @dEdge = ();
my $dEdgeOri = "";
my $dEdgeDes = "";
my $dEdgeIndex = 0;
my $dEdgeNumber = -1;
my $vCost = 4;
my $mCost = 1;

### DATA STRUCTURE:  DIRECTED_EDGE [index] [Origin] [Destination] [Cost]
for my $metal (1 .. $numMetalLayer) {     # Odd Layers: Vertical Direction   Even Layers: Horizontal Direction
    for my $row (0 .. $numTrackH-1) {
        for my $col (0 .. $numTrackV-1) {
            $dEdgeOri = "m".$metal."r".$row."c".$col;
            if ($metal % 2 == 0) { # Even Layers ==> Horizontal
                if ($vertices{$dEdgeOri}[5][0] ne "null") { # Left Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][0];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $mCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
                if ($vertices{$dEdgeOri}[5][1] ne "null") { # Right Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][1];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $mCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
                if ($vertices{$dEdgeOri}[5][4] ne "null") { # Up Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][4];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $vCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
                if ($vertices{$dEdgeOri}[5][5] ne "null") { # Down Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][5];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $vCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
            }
            else { # Odd Layers ==> Vertical
                if ($vertices{$dEdgeOri}[5][2] ne "null") { # Front Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][2];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $mCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
                if ($vertices{$dEdgeOri}[5][3] ne "null") { # Back Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][3];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $mCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
                if ($vertices{$dEdgeOri}[5][4] ne "null") { # Up Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][4];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $vCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
                if ($vertices{$dEdgeOri}[5][5] ne "null") { # Down Edge
                    $dEdgeDes = $vertices{$dEdgeOri}[5][5];
                    @dEdge = ($dEdgeIndex, $dEdgeOri, $dEdgeDes, $vCost);
                    push (@dEdges, [@dEdge]);
                    $dEdgeIndex++;
                }
            }
        }
    }
}
$dEdgeNumber = scalar @dEdges;
print "a     # dEdges            = $dEdgeNumber\n";

### UNDIRECTED EDGE Generation
### UNDIRECTED EDGE Variables
my @udEdges = ();
my @udEdge = ();
my $udEdgeTerm1 = "";
my $udEdgeTerm2 = "";
my $udEdgeIndex = 0;
my $udEdgeNumber = -1;
my $vCost = 4;
my $mCost = 1;
my $wCost = 1;

### DATA STRUCTURE:  UNDIRECTED_EDGE [index] [Term1] [Term2] [mCost] [wCost]
for my $metal (1 .. $numMetalLayer) {     # Odd Layers: Vertical Direction   Even Layers: Horizontal Direction
    for my $row (0 .. $numTrackH-1) {
        for my $col (0 .. $numTrackV-1) {
            $udEdgeTerm1 = "m".$metal."r".$row."c".$col;
            if ($metal % 2 == 0) { # Even Layers ==> Horizontal
                if ($vertices{$udEdgeTerm1}[5][1] ne "null") { # Right Edge
                    $udEdgeTerm2 = $vertices{$udEdgeTerm1}[5][1];
                    @udEdge = ($udEdgeIndex, $udEdgeTerm1, $udEdgeTerm2, $mCost, $wCost);
                    push (@udEdges, [@udEdge]);
                    $udEdgeIndex++;
                }
                if ($vertices{$udEdgeTerm1}[5][4] ne "null") { # Up Edge
                    $udEdgeTerm2 = $vertices{$udEdgeTerm1}[5][4];
                    @udEdge = ($udEdgeIndex, $udEdgeTerm1, $udEdgeTerm2, $vCost, $vCost);
                    push (@udEdges, [@udEdge]);
                    $udEdgeIndex++;
                }
            }
            else { # Odd Layers ==> Vertical
                if ($vertices{$udEdgeTerm1}[5][3] ne "null") { # Back Edge
                    $udEdgeTerm2 = $vertices{$udEdgeTerm1}[5][3];
                    @udEdge = ($udEdgeIndex, $udEdgeTerm1, $udEdgeTerm2, $mCost, $wCost);
                    push (@udEdges, [@udEdge]);
                    $udEdgeIndex++;
                }
                if ($vertices{$udEdgeTerm1}[5][4] ne "null") { # Up Edge
                    $udEdgeTerm2 = $vertices{$udEdgeTerm1}[5][4];
                    @udEdge = ($udEdgeIndex, $udEdgeTerm1, $udEdgeTerm2, $vCost, $vCost);
                    push (@udEdges, [@udEdge]);
                    $udEdgeIndex++;
                }
            }
        }
    }
}
$udEdgeNumber = scalar @udEdges;
print "a     # udEdges           = $udEdgeNumber\n";

### ZERO COST UNDIRECTED EDGE ADJUSTMENT
for my $pinIndex (0 .. $#pins) {
    if ($pins[$pinIndex][3] != -1) { # IF a pin is not outer pin
        for my $pinRowIndex (0 .. $pins[$pinIndex][3]-2) {
            my $tempRow = $pins[$pinIndex][5][$pinRowIndex];
            my $tempCol = $pins[$pinIndex][4];
            my $vName1 = "m1r".$tempRow."c".$tempCol;
            my $tempRow = $pins[$pinIndex][5][$pinRowIndex]+1;
            my $vName2 = "m1r".$tempRow."c".$tempCol;
            for my $udeIndex (0 .. $#udEdges) {
                if (($udEdges[$udeIndex][1] eq $vName1) && ($udEdges[$udeIndex][2] eq $vName2)) {
                    $udEdges[$udeIndex][3] = 0;
                }
            }
        }
    }
}


### BOUNDARY VERTICES Generation.
### DATA STRUCTURE:  Single Array includes all boundary vertices to L, R, F, B, U directions.
my @boundaryVertices = ();
my $numBoundaries = 0;

### Note, there are no boundary vertices on M1 since we do not allow M1 routing.
for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    for my $row (0 .. $numTrackH-1) {
        for my $col (0 .. $numTrackV-1) {
			if($no_vobs == 0){
				if (($row == 0 || $row == $numTrackH-1 || $col == 0 || $col == $numTrackV-1)) {
					if (($metal % 2 == 1) && ($row == 0 || $row == $numTrackH-1)) {  ## M3, M5, M7, ...
						push (@boundaryVertices, "m".$metal."r".$row."c".$col);
					}
					elsif (($metal % 2 == 0) && ($col == 0 || $col == $numTrackV-1)) {  ## M2 , M4 , M6 ....
						# Skip the boundary vertices related with power rail.   
						if ( $row % ($trackEachRow + 1) == 0 ){
							next;
						}
						push (@boundaryVertices, "m".$metal."r".$row."c".$col);
					}
				}
			}
			else{
				if (($row == 0 || $row == $numTrackH-1 || $col == $no_vobs -1 || $col == $numTrackV - ($no_vobs - 1) - 1)) {
					if (($metal % 2 == 1) && ($row == 0 || $row == $numTrackH-1)) {  ## M3, M5, M7, ...
						push (@boundaryVertices, "m".$metal."r".$row."c".$col);
					}
					elsif (($metal % 2 == 0) && ($col == $no_vobs -1 || $col == $numTrackV - ($no_vobs - 1) - 1)) {  ## M2 , M4 , M6 ....
						# Skip the boundary vertices related with power rail.   
						if ( $row % ($trackEachRow + 1) == 0 ){
							next;
						}
						push (@boundaryVertices, "m".$metal."r".$row."c".$col);
					}
				}
			}
        }
    }
}
$numBoundaries = scalar @boundaryVertices;
print "a     # Boundary Vertices = $numBoundaries\n";

# [2018-10-15] Store the net information for SON simplifying
my @outerPins = ();
my @outerPin = ();
my %h_outerPin = ();
my $numOuterPins = 0;
my $commodityInfo = -1;

for my $pinID (0 .. $#pins) {
    if ($pins[$pinID][3] == -1) {
        $commodityInfo = -1;  # Initializing

        # Find Commodity Information
        for my $netIndex (0 .. $#nets) {
            if ($nets[$netIndex][0] eq $pins[$pinID][1]){
                for my $sinkIndexofNet (0 .. $nets[$netIndex][4]){
                    if ( $nets[$netIndex][5][$sinkIndexofNet] eq $pins[$pinID][0]){
                        $commodityInfo = $sinkIndexofNet; 
                    }    
                }
            }
        }
 
        if ($commodityInfo == -1){
            print "ERROR: Cannot Find the commodity Information!!\n\n";
        }
        
        @outerPin = ($pins[$pinID][0],$pins[$pinID][1],$commodityInfo);
        push (@outerPins, [@outerPin]) ;
		$h_outerPin{$pins[$pinID][0]} = 1;
    }
}
$numOuterPins = scalar @outerPins;

### (LEFT | RIGHT | FRONT | BACK) CORNER VERTICES Generation
my @leftCorners = ();
my $numLeftCorners = 0;
my @rightCorners = ();
my $numRightCorners = 0;
my @frontCorners = ();
my $numFrontCorners = 0;
my @backCorners = ();
my $numBackCorners = 0;
my $cornerVertex = "";

for my $metal (1 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    for my $row (0 .. $numTrackH-1) {
        for my $col (0 .. $numTrackV-1) {
            $cornerVertex = "m".$metal."r".$row."c".$col;
			if ($col == 0) {
				push (@leftCorners, $cornerVertex);
				$numLeftCorners++;
			}
			if ($col == $numTrackV-1) {
				push (@rightCorners, $cornerVertex);
				$numRightCorners++;
			}
			if ($row == 0) {
				push (@frontCorners, $cornerVertex);
				$numFrontCorners++;
			}
			if ($row == $numTrackH-1) {
				push (@backCorners, $cornerVertex);
				$numBackCorners++;
			}
        }
    }
}
print "a     # Left Corners      = $numLeftCorners\n";
print "a     # Right Corners     = $numRightCorners\n";
print "a     # Front Corners     = $numFrontCorners\n";
print "a     # Back Corners      = $numBackCorners\n";

### SOURCE and SINK Generation.  All sources and sinks are supernodes.
### DATA STRUCTURE:  SOURCE or SINK [netName] [#subNodes] [Arr. of sub-nodes, i.e., vertices]
my %sources = ();
my %sinks = ();
my @source = ();
my @sink = ();
my @subNodes = ();
my $numSubNodes = 0;
my $numSources = 0;
my $numSinks = 0;

my $outerPinFlagSource = 0;
my $outerPinFlagSink = 0;
my $keyValue = "";

# Super Outer Node Keyword
my $keySON = "pinSON";

for my $pinID (0 .. $#pins) {
    @subNodes = ();
    if ($pins[$pinID][2] eq "s") { # source
        if ($pins[$pinID][3] == -1) {
            if ($SON == 1){
                if ($outerPinFlagSource == 0){
                    print "a        [SON Mode] Super Outer Node Simplifying - Source Case (Not Yet!)\n";
                    @subNodes = @boundaryVertices;
                    $outerPinFlagSource = 1;
                    $keyValue = $keySON;
                }
                else{
                    next;
                }
            }
            else{   # SON Disable
                @subNodes = @boundaryVertices;
                $keyValue = $pins[$pinID][0];
            }
        } else {
            for my $node (0 .. $pins[$pinID][3]-1) {
                push (@subNodes, "m1r".$pins[$pinID][5][$node]."c".$pins[$pinID][4]);
            }
            $keyValue = $pins[$pinID][0];
        }
        $numSubNodes = scalar @subNodes;
        @source = ($pins[$pinID][1], $numSubNodes, [@subNodes]);
        # Outer Pin should be at last in the input File Format [2018-10-15]
        $sources{$keyValue} = [@source];
    }
    elsif ($pins[$pinID][2] eq "t") { # sink
        if ($pins[$pinID][3] == -1) {
            if ( $SON == 1) {        
                if ($outerPinFlagSink == 0){
                    print "a        [SON Mode] Super Outer Node Simplifying - Sink\n";
                    @subNodes = @boundaryVertices;
                    $outerPinFlagSink = 1;
                    $keyValue = $keySON;
                }
                else{
                    next;
                }
            }
            else{ 
                @subNodes = @boundaryVertices;
                $keyValue = $pins[$pinID][0];
            }
        } else {
            for my $node (0 .. $pins[$pinID][3]-1) {
                push (@subNodes, "m1r".$pins[$pinID][5][$node]."c".$pins[$pinID][4]);
            }
            $keyValue = $pins[$pinID][0];
        }
        $numSubNodes = scalar @subNodes;
        @sink = ($pins[$pinID][1], $numSubNodes, [@subNodes]);
        $sinks{$keyValue} = [@sink];
    }
}
$numSources = keys %sources;
$numSinks = keys %sinks;
print "a     # Sources           = $numSources\n";
print "a     # Sinks             = $numSinks\n";

if ( $SON == 1){
############### Pin Information Modification #####################
    for my $pinIndex (0 .. $#pins) {
        for my $outerPinIndex (0 .. $#outerPins){
            if ($pins[$pinIndex][0] eq $outerPins[$outerPinIndex][0] ){
                $pins[$pinIndex][0] = $keySON;
                $pins[$pinIndex][1] = "Multi";
                next;
            }   
        }
    }
############ SON Node should be last elements to use pop ###########
    my $SONFlag = 0;
    while ($keySON ~~ @pins){
        $SONFlag = 1;
        @pin = pop @pins;
    }
    if ($SONFlag == 1){
        push (@pins, @pin);
    }
####################################################################
}

############### Net Information Modification from Outer pin to "SON"
if ( $SON == 1 ){
    for my $netIndex (0 .. $#nets) {
        for my $sinkIndex (0 .. $nets[$netIndex][4]-1){
            for my $outerPinIndex (0 .. $#outerPins){
                if ($nets[$netIndex][5][$sinkIndex] eq $outerPins[$outerPinIndex][0] ){
                    $nets[$netIndex][5][$sinkIndex] = $keySON;
                    next;
                }
            }
        }
        for my $pinIndex (0 .. $nets[$netIndex][2]-1){
            for my $outerPinIndex (0 .. $#outerPins){
                if ($nets[$netIndex][6][$pinIndex] eq $outerPins[$outerPinIndex][0] ){
                    $nets[$netIndex][6][$pinIndex] = $keySON;
                    next;
                }
            }
        }
    }
}

### VIRTUAL EDGE Generation
### We only define directed virtual edges since we know the direction based on source/sink information.
### All supernodes are having names starting with 'pin'.
### DATA STRUCTURE:  VIRTUAL_EDGE [index] [Origin] [Destination] [Cost=0]
my @virtualEdges = ();
my @virtualEdge = ();
my $vEdgeIndex = 0;
my $vEdgeNumber = 0;
my $virtualCost = 0;

for my $pinID (0 .. $#pins) {
    if ($pins[$pinID][2] eq "s") { # source
        if(exists $sources{$pins[$pinID][0]}){
            for my $term (0 .. $sources{$pins[$pinID][0]}[1]-1){
                @virtualEdge = ($vEdgeIndex, $pins[$pinID][0], $sources{$pins[$pinID][0]}[2][$term], $virtualCost);
                push (@virtualEdges, [@virtualEdge]);
                $vEdgeIndex++;
            }
        }
    }
    elsif ($pins[$pinID][2] eq "t") { # sink
        if(exists $sinks{$pins[$pinID][0]}){
            for my $term (0 ..  $sinks{$pins[$pinID][0]}[1]-1){
                @virtualEdge = ($vEdgeIndex, $sinks{$pins[$pinID][0]}[2][$term], $pins[$pinID][0], $virtualCost);
                push (@virtualEdges, [@virtualEdge]);
                $vEdgeIndex++;
            }
        }
    }
}

$vEdgeNumber = scalar @virtualEdges;
print "a     # Virtual Edges     = $vEdgeNumber\n";

### END:  DATA STRUCTURE ##############################################################################################


### CPLEX Variable Rule
# Variables can be named anything provided that the name does not exceed 255 characters, 
# all of which must be alphanumeric (a-z, A-Z, 0-9) or one of these symbols: 
# ! " # $ % & ( ) , . ; ? @ _ ‘ ’ { } ~. 
# Longer names are truncated to 255 characters. A variable name can not begin with a 
# number or a period.  The letter E or e, alone or followed by other valid symbols, or 
# followed by another E or e, should be avoided as this notation is reserved for 
# exponential entries. 

print "a   Creating ILP Formulation with respect to CPLEX LP file format.\n";
print "a   * Note1. We assume uni-directional routing per each metal layer. [ODD:V, EVEN:H])\n";
print "a   * Note2. We prevent from having horizontal metal segments on power lines.\n";
print "a     0. Objective Function ";

open (my $out, '>', $outfile);

### INIT
print $out "\\\\  ILP Formulation for CPLEX\n";
print $out "\\\\    Authors:     ilgweon Kang, Dongwon Park, Daeyeal Lee, Chung-Kuan Cheng\n";
print $out "\\\\    Version: 1.0\n";
print $out "\\\\    Input File:  $workdir/$infile\n";
print $out "\\\\    DO NOT DISTRIBUTE IN ANY PURPOSE! \n\n";

print $out "\\\\  Layout Information \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\n";
print $out "\\\\    # Vertical Tracks   = $numTrackV\n";
print $out "\\\\    # Horizontal Tracks = $numTrackH\n";
print $out "\\\\    # Nets              = $totalNets\n";
print $out "\\\\      List of Nets      = ";
foreach my $key (keys %h_nets) {
    print $out "$key ";
}
print $out "\n";
print $out "\\\\    # Pins              = $totalPins\n";
print $out "\\\\    # Sources           = $numSources\n";
print $out "\\\\      List of Sources   = ";
foreach my $key (keys %sources) {
    print $out "$key ";
}
print $out "\n";
print $out "\\\\    # Sinks             = $numSinks\n";
print $out "\\\\      List of Sinks     = ";
foreach my $key (keys %sinks) {
    print $out "$key ";
}


print $out "\n";
print $out "\\\\    # Outer Pins        = $numOuterPins\n";
print $out "\\\\      List of Outer Pins= ";
for my $i (0 .. $#outerPins) {              # All SON (Super Outer Node)
    print $out "$outerPins[$i][0] ";        # 0 : Pin number , 1 : net number
}

print $out "\n";
print $out "\\\\      Outer Pins Information= ";
for my $i (0 .. $#outerPins) {              # All SON (Super Outer Node)
    print $out " $outerPins[$i][1]=$outerPins[$i][2] ";        # 0 : Net number , 1 : Commodity number
}
print $out "\n";
print $out "\n\n";

print $out "\\\\\\ Begin ILP Formulation \\\\\\\\\\\\\\\\\\\\\\\\\n\n";
### OBJ
print $out "\\\\\\ Objective \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\n";
print $out "Minimize\n";
print $out "ANS\n\n\n";

### CONST
print $out "\\\\\\ Constraints \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\n";
print $out "Subject to\n";
print $out "ANS - ANS_WL - ANS_ML = 0\n\n";


### ANS_WIRELENGTH
print $out "ANS_WL ";
for my $udeIndex (0 .. $#udEdges) {
    print $out "- $udEdges[$udeIndex][4] W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
}
for my $vEdgeIndex (0 .. $#virtualEdges) {
    print $out "- $virtualEdges[$vEdgeIndex][3] W($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
}
print $out "= 0\n\n";

### ANS_METALLENGTH
print $out "ANS_ML ";
for my $udeIndex (0 .. $#udEdges) {
    print $out "- $udEdges[$udeIndex][3] M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
}
for my $vEdgeIndex (0 .. $#virtualEdges) {
    print $out "- $virtualEdges[$vEdgeIndex][3] M($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
}
print $out "= 0\n\n\n";
print "has been written.\n";


my %edge_in = ();
my %edge_out = ();
for my $edge (0 .. @dEdges-1){
	push @{ $edge_out{$dEdges[$edge][1]} }, $edge;
	push @{ $edge_in{$dEdges[$edge][2]} }, $edge;
}
my %vedge_in = ();
my %vedge_out = ();
for my $edge (0 .. @virtualEdges-1){
	push @{ $vedge_out{$virtualEdges[$edge][1]} }, $edge;
	push @{ $vedge_in{$virtualEdges[$edge][2]} }, $edge;
}

### COMMODITY FLOW Conservation
# [SON Enable : No Change]
print "a     1. Commodity flow conservation ";
print $out "\\ 1. Commodity flow conservation for each vertex and every connected edge to the vertex\n";
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $metal (1 .. $numMetalLayer) {   
            for my $row (0 .. $numTrackH-1) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "C$commodityIndex\_";
                    print $out "V($vName) ";
					for my $i (0 .. $#{$edge_in{$vName}}){ # incoming
						print $out "+ ";
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($dEdges[$edge_in{$vName}[$i]][1])($vName) ";
					}
					for my $i (0 .. $#{$edge_out{$vName}}){ # outgoing
						print $out "- ";
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($vName)($dEdges[$edge_out{$vName}[$i]][2]) ";
					}
					for my $i (0 .. $#{$vedge_in{$vName}}){ # sink
						print $out "+ ";
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($virtualEdges[$vedge_in{$vName}[$i]][1])($vName) ";
						print $out "- ";
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($vName)($virtualEdges[$vedge_in{$vName}[$i]][1]) ";
					}
					for my $i (0 .. $#{$vedge_out{$vName}}){ # source
						print $out "- ";
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($vName)($virtualEdges[$vedge_out{$vName}[$i]][2]) ";
						print $out "+ ";
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($virtualEdges[$vedge_out{$vName}[$i]][2])($vName) ";
					}
                    print $out "= 0\n";
                }
            }
        }
        for my $pinIndex (0 .. $#pins) {
            $vName = $pins[$pinIndex][0];
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "V($vName) ";
			for my $i (0 .. $#{$vedge_in{$vName}}){ # sink
				print $out "+ ";
				print $out "N$nets[$netIndex][1]\_";
				print $out "C$commodityIndex\_";
				print $out "E($virtualEdges[$vedge_in{$vName}[$i]][1])($vName) ";
				print $out "- ";
				print $out "N$nets[$netIndex][1]\_";
				print $out "C$commodityIndex\_";
				print $out "E($vName)($virtualEdges[$vedge_in{$vName}[$i]][1]) ";
			}
			for my $i (0 .. $#{$vedge_out{$vName}}){ # source
				print $out "- ";
				print $out "N$nets[$netIndex][1]\_";
				print $out "C$commodityIndex\_";
				print $out "E($vName)($virtualEdges[$vedge_out{$vName}[$i]][2]) ";
				print $out "+ ";
				print $out "N$nets[$netIndex][1]\_";
				print $out "C$commodityIndex\_";
				print $out "E($virtualEdges[$vedge_out{$vName}[$i]][2])($vName) ";
			}
            print $out "= 0\n";
        }
        print $out "\n";
    }
}
print $out "\n";
print "has been written.\n";

### Exclusiveness use of VERTEX.  (Only considers incoming flows by nature.)
print "a     2. Exclusiveness use of vertex ";
print $out "\\ 2. Exclusiveness use of vertex for each vertex and every connected edge to the vertex\n";
for my $metal (1 .. $numMetalLayer) {   
    for my $row (0 .. $numTrackH-1) {
        for my $col (0 .. $numTrackV-1) {
            my $isFirstTerm = 1;
            $vName = "m".$metal."r".$row."c".$col;
            for my $netIndex (0 .. $#nets) {
				for my $i (0 .. $#{$edge_in{$vName}}){ # incoming
					if ($isFirstTerm != 1) {
						print $out "+ ";
					}
					$isFirstTerm = 0;
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($dEdges[$edge_in{$vName}[$i]][1])($vName) ";
				}
				for my $i (0 .. $#{$vedge_in{$vName}}){ # incoming
					if ($isFirstTerm != 1) {
						print $out "+ ";
					}
					$isFirstTerm = 0;
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($virtualEdges[$vedge_in{$vName}[$i]][1])($vName) ";
				}
            }
            print $out "<= 1\n";
        }
    }
}

# [SON : In SON node, remove the exclusiveness]
for my $pinIndex (0 .. $#pins) {
    my $isSource = -1;
    my $isFirstTerm = 1;
    $vName = $pins[$pinIndex][0];

    if (($SON == 1) && ($vName eq $keySON)){  # SON Enable : Sin
        next;
   }
    else{
        for my $netIndex (0 .. $#nets) {
        ### VIRTUAL_EDGE [index] [Origin] [Destination] [Cost=0]
            for my $vEdgeIndex (0 .. $#virtualEdges) {
                if ($vName eq $virtualEdges[$vEdgeIndex][2]) { # sink
                    $isSource = 0;
                    if ($isFirstTerm != 1) {
                        print $out "+ ";
                    }
                    $isFirstTerm = 0;
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "E($virtualEdges[$vEdgeIndex][1])($vName) ";
                }
                if ($vName eq $virtualEdges[$vEdgeIndex][1]) { # source
                    $isSource = 1;
                    if ($isFirstTerm != 1) {
                        print $out "+ ";
                    }
                    $isFirstTerm = 0;
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "E($virtualEdges[$vEdgeIndex][2])($vName) ";
                }
            }
        }
        if ($isSource == 1) {
            print $out "<= 0\n";
        }
        elsif ($isSource == 0) {
            print $out "<= 1\n";
        }
    }
}
print $out "\n\n";
print "has been written.\n";

### EDGE assignment  (Assign edges based on commodity information.)
print "a     3. Edge assignment ";
print $out "\\ 3. Edge assignment for each edge for every net\n";
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $udeIndex (0 .. $#udEdges) {
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
            print $out ">= 0\n";
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) ";
            print $out ">= 0\n";
        }
        for my $vEdgeIndex (0 .. $#virtualEdges) {
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
            print $out ">= 0\n";
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) ";
            print $out ">= 0\n";
        }
        print $out "\n";
    }
}
print $out "\n";
print "has been written.\n";


### Exclusiveness use of EDGES + Metal segment assignment by using edge usage information
print "a     4. Exclusiveness use of edge ";
print $out "\\ 4. Exclusiveness use of each edge + Metal segment assignment by using edge usage information\n";
for my $udeIndex (0 .. $#udEdges) {
	if(!exists($h_obs_remove{"($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
		print $out "M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
		for my $netIndex (0 .. $#nets) {
			print $out "- ";
			print $out "N$nets[$netIndex][1]\_";
			print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
			print $out "- ";
			print $out "N$nets[$netIndex][1]\_";
			print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) ";
		}
		print $out "= 0\n";
	}
	else{
	}
}
for my $vEdgeIndex (0 .. $#virtualEdges) {
    print $out "M($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
    for my $netIndex (0 .. $#nets) {
        print $out "- ";
        print $out "N$nets[$netIndex][1]\_";
        print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
        print $out "- ";
        print $out "N$nets[$netIndex][1]\_";
        print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) ";
    }
    print $out "= 0\n";
}
print $out "\n";
print $out "\n";

print "has been written.\n";

### Wire assignment by using commodity flow information
print "a     5. Wire assignment ";
print $out "\\ 5. Wire assignment by using commodity flow information\n";
for my $udeIndex (0 .. $#udEdges) {
    print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
    for my $netIndex (0 .. $#nets) {
        for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) ";
        }
    }
    print $out "<= 0\n";
    for my $netIndex (0 .. $#nets) {
        for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
            print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
            print $out ">= 0\n";
            print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) ";
            print $out ">= 0\n";
        }
    }
}
for my $vEdgeIndex (0 .. $#virtualEdges) {
    print $out "W($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
    for my $netIndex (0 .. $#nets) {
        for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) ";
        }
    }
    print $out "<= 0\n";
    for my $netIndex (0 .. $#nets) {
        for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
            print $out "W($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
            print $out ">= 0\n";
            print $out "W($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) ";
            print $out "- ";
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) ";
            print $out ">= 0\n";
        }
    }
}
print $out "\n\n";
print "has been written.\n";


### Geometry variables for LEFT, RIGHT, FRONT, BACK directions
print "a     6. Geometric variables ";
print $out "\\ 6. Geometry variables for Left (GL), Right (GR), Front (GF), and Back (GB) directions\n";
### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
print $out "\\ 6-A. Geometry variables for Left-tip on each vertex\n";
for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    if ($metal % 2 == 1) {
        next;
    }
    else {
        for my $row (0 .. $numTrackH-1) {
            for my $col (0 .. $numTrackV-1) {
                $vName = "m".$metal."r".$row."c".$col;
                print $out "GL_V($vName) ";
                print $out "+ M";
                if ($vertices{$vName}[5][0] ne "null") {
                    print $out "($vertices{$vName}[5][0])($vName) ";
                }
                elsif ($vertices{$vName}[5][0] eq "null") {
                    print $out "(LeftEnd)($vName) ";
                }
                print $out "<= 1\n";
                print $out "GL_V($vName) ";
                print $out "- M";
                if ($vertices{$vName}[5][1] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][1]) ";
                }
                elsif ($vertices{$vName}[5][1] eq "null") {
                    print $out "($vName)(RightEnd) ";
                }
                print $out "<= 0\n";
                print $out "GL_V($vName) ";
                print $out "+ M";
                if ($vertices{$vName}[5][0] ne "null") {
                    print $out "($vertices{$vName}[5][0])($vName) ";
                }
                elsif ($vertices{$vName}[5][0] eq "null") {
                    print $out "(LeftEnd)($vName) ";
                }
                print $out "- M";
                if ($vertices{$vName}[5][1] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][1]) ";
                }
                elsif ($vertices{$vName}[5][1] eq "null") {
                    print $out "($vName)(RightEnd) ";
                }
                print $out ">= 0\n";
            } 
        }
    }
}
print $out "\n";
### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
print $out "\\ 6-B. Geometry variables for Right-tip on each vertex\n";
for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    if ($metal % 2 == 1) {
        next;
    }
    else {
        for my $row (0 .. $numTrackH-1) {
            for my $col (0 .. $numTrackV-1) {
                $vName = "m".$metal."r".$row."c".$col;
                print $out "GR_V($vName) ";
                print $out "- M";
                if ($vertices{$vName}[5][0] ne "null") {
                    print $out "($vertices{$vName}[5][0])($vName) ";
                }
                elsif ($vertices{$vName}[5][0] eq "null") {
                    print $out "(LeftEnd)($vName) ";
                }
                print $out "<= 0\n";
                print $out "GR_V($vName) ";
                print $out "+ M";
                if ($vertices{$vName}[5][1] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][1]) ";
                }
                elsif ($vertices{$vName}[5][1] eq "null") {
                    print $out "($vName)(RightEnd) ";
                }
                print $out "<= 1\n";
                print $out "GR_V($vName) ";
                print $out "- M";
                if ($vertices{$vName}[5][0] ne "null") {
                    print $out "($vertices{$vName}[5][0])($vName) ";
                }
                elsif ($vertices{$vName}[5][0] eq "null") {
                    print $out "(LeftEnd)($vName) ";
                }
                print $out "+ M";
                if ($vertices{$vName}[5][1] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][1]) ";
                }
                elsif ($vertices{$vName}[5][1] eq "null") {
                    print $out "($vName)(RightEnd) ";
                }
                print $out ">= 0\n";
            }
        }
    }
}
print $out "\n";
### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
print $out "\\ 6-C. Geometry variables for Front-tip on each vertex\n";
for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    if ($metal % 2 == 1) {
        for my $row (0 .. $numTrackH-1) {
            for my $col (0 .. $numTrackV-1) {
                $vName = "m".$metal."r".$row."c".$col;
                print $out "GF_V($vName) ";
                print $out "+ M";
                if ($vertices{$vName}[5][2] ne "null") {
                    print $out "($vertices{$vName}[5][2])($vName) ";
                }
                elsif ($vertices{$vName}[5][2] eq "null") {
                    print $out "(FrontEnd)($vName) ";
                }
                print $out "<= 1\n";
                print $out "GF_V($vName) ";
                print $out "- M";
                if ($vertices{$vName}[5][3] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][3]) ";
                }
                elsif ($vertices{$vName}[5][3] eq "null") {
                    print $out "($vName)(BackEnd) ";
                }
                print $out "<= 0\n";
                print $out "GF_V($vName) ";
                print $out "+ M";
                if ($vertices{$vName}[5][2] ne "null") {
                    print $out "($vertices{$vName}[5][2])($vName) ";
                }
                elsif ($vertices{$vName}[5][2] eq "null") {
                    print $out "(FrontEnd)($vName) ";
                }
                print $out "- M";
                if ($vertices{$vName}[5][3] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][3]) ";
                }
                elsif ($vertices{$vName}[5][3] eq "null") {
                    print $out "($vName)(BackEnd) ";
                }
                print $out ">= 0\n";
            }
        }
    }
    else {
        next;
    }
}
print $out "\n";
### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
print $out "\\ 6-D. Geometry variables for Front-tip on each vertex\n";
for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    if ($metal % 2 == 1) {
        for my $row (0 .. $numTrackH-1) {
            for my $col (0 .. $numTrackV-1) {
                $vName = "m".$metal."r".$row."c".$col;
                print $out "GB_V($vName) ";
                print $out "- M";
                if ($vertices{$vName}[5][2] ne "null") {
                    print $out "($vertices{$vName}[5][2])($vName) ";
                }
                elsif ($vertices{$vName}[5][2] eq "null") {
                    print $out "(FrontEnd)($vName) ";
                }
                print $out "<= 0\n";
                print $out "GB_V($vName) ";
                print $out "+ M";
                if ($vertices{$vName}[5][3] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][3]) ";
                }
                elsif ($vertices{$vName}[5][3] eq "null") {
                    print $out "($vName)(BackEnd) ";
                }
                print $out "<= 1\n";
                print $out "GB_V($vName) ";
                print $out "- M";
                if ($vertices{$vName}[5][2] ne "null") {
                    print $out "($vertices{$vName}[5][2])($vName) ";
                }
                elsif ($vertices{$vName}[5][2] eq "null") {
                    print $out "(FrontEnd)($vName) ";
                }
                print $out "+ M";
                if ($vertices{$vName}[5][3] ne "null") {
                    print $out "($vName)($vertices{$vName}[5][3]) ";
                }
                elsif ($vertices{$vName}[5][3] eq "null") {
                    print $out "($vName)(BackEnd) ";
                }
                print $out ">= 0\n";
            }
        }
    }
    else {
        next;
    }
}
print $out "\n\n";
print "have been written.\n";


print "a     7. Minimum area rule ";
print $out "\\ 7. Minimum Area Rule\n";

if ( $MAR_Parameter == 0 ){
    print "is disable\n";
    print $out "\\ MAR is disable\n";
}
else{  # PRL Rule Enable /Disable

### Minimum Area Rule to prevent from having small metal segment
     for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 0) {  # M2/
            for my $row (0 .. $numTrackH-1) {
                for my $col (0 .. $numTrackV - $MAR_Parameter) {
                    for my $marIndex (0 .. $MAR_Parameter-1){
                        my $colNumber = $col + $marIndex;
                        my $varName = "m".$metal."r".$row."c".$colNumber;
                        if ($marIndex != 0){
                            print $out "+ ";
                        }
                        print $out "GL_V($varName) + GR_V($varName) ";

                    }
                    print $out "<= 1\n";
                }
            }
        }
        else {  # M1, M3
            my $MaxIndex = $MAR_Parameter-1;
            if ($DoublePowerRail == 1){
                $MaxIndex--;
            }
                        
            for my $row (0 .. $numTrackH - 1 - $MaxIndex) {
                for my $col (0 .. $numTrackV-1) {

                    my $powerRailFlag = 0; 
					my $powerRailIndex = 0; 
                    my $varName = "m".$metal."r".$row."c".$col;
                    my $newRow = $row;

                    if( ($vertices{$varName}[5][3] eq "null") || (( $DoublePowerRail == 1) && (($newRow + 1) % ($trackEachRow + 1) == 0) && ($MAR_Parameter == 2)) ){
                        next;  # Skip to generate the constraint for this condition.
                    }

                    for my $marIndex (0 .. $MAR_Parameter-1){
                        # Double Power Rail
                        $powerRailIndex = ceil($marIndex / ($trackEachRow + 2));
                        if ( ($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($powerRailFlag < $powerRailIndex) ){
                            $powerRailFlag++;
                            $newRow++;
                            next;
                        }
                        else{
                            if ($marIndex != 0){
                                print $out "+ ";
                            }
                            print $out "GF_V($varName) + GB_V($varName) ";
                            $newRow++;
                            $varName = $vertices{$varName}[5][3];
                            if ($varName eq "null"){
                                last;
                            }
                        }
                    }
                    print $out "<= 1\n";
                }
            }
        }
    }
    print $out "\n\n";
    print "has been written.\n";
}


print "a     8. Tip-to-Tip spacing rule ";
print $out "\\ 8. Tip-to-Tip Spacing Rule\n";
if ( $EOL_Parameter == 0 ){
    print "is disable\n";
    print $out "\\ EOL is disable\n";
}
else{  # PRL Rule Enable /Disable
### Tip-to-Tip Spacing Rule to prevent from having too close metal tips.
### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
	print $out "\\ 8-A. from Right Tip to Left Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 0) {  # M2
            for my $row (0 .. $numTrackH-1) {
                
                # skip the EOL rule related with power Rail.
                if ($row % ($trackEachRow + 1) == 0 ){
                    next;
                }

                for my $col (0 .. $numTrackV - 2) { 
                    $vName = "m".$metal."r".$row."c".$col;

                    # FR Direction Checking
                    my $vName_FR = $vertices{$vName}[5][7];
                    if ( ($vName_FR ne "null") && ($row % ($trackEachRow + 1) != 1) && ($EOL_Parameter >= 2)) {
                        print $out "GR_V($vName) + ";
                        for my $eolIndex (0 .. $EOL_Parameter-2){  
                            print $out "GL_V($vName_FR) ";
                            if ($eolIndex != ($EOL_Parameter-2)){
                                $vName_FR = $vertices{$vName_FR}[5][1];
                                if ($vName_FR eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }

                    # R Direction Checking
                    my $vName_R = $vertices{$vName}[5][1];
                    if ($vName_R ne "null") {
                        print $out "GR_V($vName) + ";
                        for my $eolIndex (0 .. $EOL_Parameter-1){
                            print $out "GL_V($vName_R) ";
                            if ($eolIndex != $EOL_Parameter-1){
                                $vName_R = $vertices{$vName_R}[5][1];
                                if ($vName_R eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }

                    # BR Direction Checking 
                    my $vName_BR = $vertices{$vName}[5][9];
                    if ( ($vName_BR ne "null") && ($row % ($trackEachRow + 1) != $trackEachRow) && ($EOL_Parameter >= 2)) {
                        print $out "GR_V($vName) + ";
                        for my $eolIndex (0 .. $EOL_Parameter-2){  
                            print $out "GL_V($vName_BR) ";
                            if ($eolIndex != ($EOL_Parameter-2)){
                                $vName_BR = $vertices{$vName_BR}[5][1];
                                if ($vName_BR eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                }
            }
        }
    }
    print $out "\n";

### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    print $out "\\ 8-B. from Left Tip to Right Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 0) {
            for my $row (0 .. $numTrackH-1) {

                # skip the EOL rule related with power Rail.
                if ($row % ($trackEachRow + 1) == 0 ){
                    next;
                }

                for my $col (1 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;

                    # FL Direction Checking
                    my $vName_FL = $vertices{$vName}[5][6];
                    if (($vName_FL ne "null") && ($row % ($trackEachRow + 1) != 1) && ($EOL_Parameter >= 2)) {
                        print $out "GL_V($vName) + ";
                        for my $eolIndex (0 .. $EOL_Parameter-2){  
                            print $out "GR_V($vName_FL) ";
                            if ($eolIndex != ($EOL_Parameter-2)){
                                $vName_FL = $vertices{$vName_FL}[5][0];
                                if ($vName_FL eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }

                    # L Direction Checking
                    my $vName_L = $vertices{$vName}[5][0];
                    if ($vName_L ne "null") {
                        print $out "GL_V($vName) + ";
                        for my $eolIndex (0 .. $EOL_Parameter-1){
                            print $out "GR_V($vName_L) ";
                            if ($eolIndex != $EOL_Parameter-1){
                                $vName_L = $vertices{$vName_L}[5][0];
                                if ($vName_L eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }

                    # BL Direction Checking 
                    my $vName_BL = $vertices{$vName}[5][8];
                    if ( ($vName_BL ne "null") && ($row % ($trackEachRow + 1) != $trackEachRow) && ($EOL_Parameter >= 2)) {
                        print $out "GL_V($vName) + ";
                        for my $eolIndex (0 .. $EOL_Parameter-2){  
                            print $out "GR_V($vName_BL) ";
                            if ($eolIndex != ($EOL_Parameter-2)){
                                $vName_BL = $vertices{$vName_BL}[5][0];
                                if ($vName_BL eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                }
            }
        }
    }
    print $out "\n";


### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
#
##### one Power Rail vertice has 2 times cost of other vertices.
#
    print $out "\\ 8-C. from Back Tip to Front Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 1) {
            for my $row (0 .. $numTrackH-2) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;

                    # BL Direction Checking
                    my $vName_BL = $vertices{$vName}[5][8];
                    if (($vName_BL ne "null") && ($EOL_Parameter >= 2)) {
                        my $newRow = $row + 1;
                        if ( ($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($EOL_Parameter == 2)){ # Skip the BR Direction
                            ### Nothing
                        }
                        else{
                            print $out "GB_V($vName)"; 
                            my $powerRailFlag = 0; my $powerRailIndex = 0;
                            for my $eolIndex (1 .. $EOL_Parameter-1){
                                $powerRailIndex = ceil($eolIndex / ($trackEachRow + 2));
                                if ( ($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($powerRailFlag < $powerRailIndex)){
                                    $powerRailFlag++;
                                    next;
                                }
                                print $out " + GF_V($vName_BL)";
                                if ( ($eolIndex) < ($EOL_Parameter-1)){
                                    $vName_BL = $vertices{$vName_BL}[5][3];
                                    $newRow++;
                                    if (($vName_BL eq "null")){
                                        last;
                                    }
                                }
                            }
                            print $out " <= 1\n";
                        }
                    }

                    # B Direction Checking
                    my $vName_B = $vertices{$vName}[5][3];
                    if ($vName_B ne "null") {
                        my $newRow = $row + 1;
                        if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($EOL_Parameter == 1)){ # Skip the B Direction
                            ### Nothing
                        }
                        else{
                            print $out "GB_V($vName)";
                            my $powerRailFlag = 0; my $powerRailIndex = 0;
                            for my $eolIndex (1 .. $EOL_Parameter){
                                $powerRailIndex = ceil($eolIndex / ($trackEachRow + 2));
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($powerRailFlag < $powerRailIndex )){
                                    $powerRailFlag++;
                                    next;
                                }   
                                print $out " + GF_V($vName_B)";
                                if ($eolIndex < $EOL_Parameter){
                                    $vName_B = $vertices{$vName_B}[5][3];
                                    $newRow++;
                                    if ($vName_B eq "null"){
                                        last;
                                    }
                                }
                            }
                            print $out " <= 1\n";
                        }
                    }

                    # BR Direction Checking 
                    my $vName_BR = $vertices{$vName}[5][9];
                    if (($vName_BR ne "null") && ($EOL_Parameter >= 2)) {
                        my $newRow = $row + 1;
                        if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($EOL_Parameter == 2)){ # Skip the BL Direction
                            ### Nothing
                        }   
                        else{
                            print $out "GB_V($vName)";
                            my $powerRailFlag = 0; my $powerRailIndex = 0;
                            for my $eolIndex (1 .. $EOL_Parameter-1){
                                $powerRailIndex = ceil($eolIndex / ($trackEachRow + 2));
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($powerRailFlag < $powerRailIndex)){
                                    $powerRailFlag++;
                                    next;
                                }
                                print $out " + GF_V($vName_BR)";
                                if ($eolIndex < ($EOL_Parameter-1)){
                                    $vName_BR = $vertices{$vName_BR}[5][3];
                                    $newRow++;
                                    if ($vName_BR eq "null"){
                                        last;
                                    }
                                }
                            }
                            print $out " <= 1\n";
                        }
                    }
                }
            }
        }
    }
    print $out "\n";

### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    print $out "\\ 8-D. from Front Tip to Back Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 1) {
            for my $row (1 .. $numTrackH-1) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;

                    # FL Direction
                    my $vName_FL = $vertices{$vName}[5][6];
                    if (($vName_FL ne "null") && ($EOL_Parameter >= 2)) {
                        my $newRow = $row - 1;
                        if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($EOL_Parameter == 2)){ # Skip the BR Direction
                            ### Nothing
                        }
                        else{
                            print $out "GF_V($vName)"; 
                            my $powerRailFlag = 0; my $powerRailIndex = 0;
                            for my $eolIndex (1 .. $EOL_Parameter-1){
                                $powerRailIndex = ceil($eolIndex / ($trackEachRow + 2));
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($powerRailFlag < $powerRailIndex)){
                                    $powerRailFlag++;
                                    next;
                                }
                                print $out " + GB_V($vName_FL)";
                                if ( ($eolIndex) < ($EOL_Parameter-1)){
                                    $vName_FL = $vertices{$vName_FL}[5][2];
                                    $newRow--;
                                    if (($vName_FL eq "null")){
                                        last;
                                    }
                                }
                            }
                            print $out " <= 1\n";
                        }
                    }

                    # F Direction Checking
                    my $vName_F = $vertices{$vName}[5][2];
                    if ($vName_F ne "null") {
                        my $newRow = $row - 1;
                        if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($EOL_Parameter == 1)){ # Skip the B Direction
                            ### Nothing
                        }
                        else{
                            print $out "GF_V($vName)";
                            my $powerRailFlag = 0; my $powerRailIndex = 0;
                            for my $eolIndex (1 .. $EOL_Parameter){
                                $powerRailIndex = ceil($eolIndex / ($trackEachRow + 2));
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($powerRailFlag < $powerRailIndex )){
                                    $powerRailFlag++;
                                    next;
                                }   
                                print $out " + GB_V($vName_F)";
                                if ($eolIndex < $EOL_Parameter){
                                    $vName_F = $vertices{$vName_F}[5][2];
                                    $newRow--;
                                    if ($vName_F eq "null"){
                                        last;
                                    }
                                }
                            }
                            print $out " <= 1\n";
                        }
                    }

                    # FR Direction
                    my $vName_FR = $vertices{$vName}[5][7];
                    if (($vName_FR ne "null") && ($EOL_Parameter >= 2)) {
                        my $newRow = $row - 1;
                        if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($EOL_Parameter == 2)){ # Skip the BR Direction
                            ### Nothing
                        }
                        else{
                            print $out "GF_V($vName)"; 
                            my $powerRailFlag = 0; my $powerRailIndex = 0;
                            for my $eolIndex (1 .. $EOL_Parameter-1){
                                $powerRailIndex = ceil($eolIndex / ($trackEachRow + 2));
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($powerRailFlag < $powerRailIndex)){
                                    $powerRailFlag++;
                                    next;
                                }
                                print $out " + GB_V($vName_FR)";
                                if ( ($eolIndex) < ($EOL_Parameter-1)){
                                    $vName_FR = $vertices{$vName_FR}[5][2];
                                    $newRow--;
                                    if (($vName_FR eq "null")){
                                        last;
                                    }
                                }
                            }
                            print $out " <= 1\n";
                        }
                    }
                }
            }
        }
    }
    print $out "\n\n";
    print "has been written.\n";
}

print "a     9. Via-to-via spacing rule ";
print $out "\\ 9. Via-to-Via Spacing Rule\n";
if ( $VR_Parameter == 0 ){
    print "is disable\n";
    print $out "\\ VR is disable\n";
}
else{  # VR Rule Enable /Disable
### Via-to-Via Spacing Rule to prevent from having too close vias and stacked vias.
### UNDIRECTED_EDGE [index] [Term1] [Term2] [Cost]
### VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    my $maxDistRow = $numTrackH-1;
    my $maxDistCol = $numTrackV-1;

    for my $metal (1 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        for my $row (0 .. $numTrackH-1) {
            for my $col (0 .. $numTrackV-1) {            
                if (($row == $numTrackH-1) && ($col == $numTrackV-1)) {
                    next;
                }
				$vName = "m".$metal."r".$row."c".$col;
                if ($vertices{$vName}[5][4] ne "null") { # Up Neighbor, i.e., VIA from the vName vertex.
					my $tmp_out = "";
					my $prev_cnt_row = -1;
                    for my $newRow ($row .. $numTrackH-1) {
						my $cnt_row = 0;
						my $tmp_str = "";
                        for my $newCol ($col .. $numTrackV-1) {
                            my $distCol = $newCol - $col;
                            my $distRow = $newRow - $row;

                            # Check power rail between newRow and row. (Double Power Rail Rule Applying
                            if ( ($DoublePowerRail == 1) && (floor($newRow / ($trackEachRow + 1)) ne floor($row / ($trackEachRow + 1))) ){
                                $distRow++;
                            }
                            if ( ($newRow eq $row) && ($newCol eq $col) ){  # Initial Value.
								$cnt_row++;
                                next;
                            }

                            if ( ($distCol * $distCol + $distRow * $distRow) > ($VR_Parameter * $VR_Parameter) ){ # Check the Via Distance
                                last;
                            }
                            ###### # Need to consider the Power rail distance by 2 like EOL rule
                            my $neighborName = $vName;
                            while ($distCol > 0){
                                $distCol--;
                                $neighborName = $vertices{$neighborName}[5][1];
                                if ($neighborName eq "null"){
                                    last;
                                }
                            }

                            my $currentRow = $row; my $FlagforSecond = 0;
                            while ($distRow > 0){  
                                $distRow--; 
                                $currentRow++;

                                if( ($DoublePowerRail == 1) && ($currentRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0) ){ #power Rail
                                    $FlagforSecond = 1;
                                    $currentRow--; 
                                    next;
                                }
                                $FlagforSecond = 0;
                                $neighborName = $vertices{$neighborName}[5][3];
                                if ($neighborName eq "null"){
                                    last;
                                }
                            }
                            my $neighborUp = "";
                            if ($neighborName ne "null"){
                                $neighborUp = $vertices{$neighborName}[5][4];
                                if ($neighborUp eq "null"){
                                    print "ERROR : There is some bug in switch box definition !\n";
                                    exit(-1);
                                }
                            }
							# Via-to-via Spacing Rule
							$tmp_str = $tmp_str."+ M($neighborName)($neighborUp) ";
							$cnt_row++;
                        }
						if($prev_cnt_row == -1){
							$prev_cnt_row = $cnt_row;
							$tmp_out = $tmp_str;
						}
						else{
							if($prev_cnt_row == $cnt_row){
								$tmp_out = $tmp_out.$tmp_str;
							}
							else{
								print $out "M($vName)($vertices{$vName}[5][4]) ";
								print $out $tmp_out;
								print $out "<= 1\n";
								last;
							}
						}
                    }

					my $tmp_out = "";
					my $prev_cnt_col = -1;
					for my $newCol ($col .. $numTrackV-1) {
						my $cnt_col = 0;
						my $tmp_str = "";
							for my $newRow ($row .. $numTrackH-1) {
                            my $distCol = $newCol - $col;
                            my $distRow = $newRow - $row;

                            # Check power rail between newRow and row. (Double Power Rail Rule Applying
                            if ( ($DoublePowerRail == 1) && (floor($newRow / ($trackEachRow + 1)) ne floor($row / ($trackEachRow + 1))) ){
                                $distRow++;
                            }
                            if ( ($newRow eq $row) && ($newCol eq $col) ){  # Initial Value.
								$cnt_col++;
                                next;
                            }

                            if ( ($distCol * $distCol + $distRow * $distRow) > ($VR_Parameter * $VR_Parameter) ){ # Check the Via Distance
                                last;
                            }
                            
                            ###### # Need to consider the Power rail distance by 2 like EOL rule
                            my $neighborName = $vName;
                            while ($distCol > 0){
                                $distCol--;
                                $neighborName = $vertices{$neighborName}[5][1];
                                if ($neighborName eq "null"){
                                    last;
                                }
                            }

                            my $currentRow = $row; my $FlagforSecond = 0;
                            while ($distRow > 0){  
                                $distRow--; 
                                $currentRow++;

                                if( ($DoublePowerRail == 1) && ($currentRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0) ){ #power Rail
                                    $FlagforSecond = 1;
                                    $currentRow--; 
                                    next;
                                }
                                $FlagforSecond = 0;
                                $neighborName = $vertices{$neighborName}[5][3];
                                if ($neighborName eq "null"){
                                    last;
                                }
                            }
                            my $neighborUp = "";
                            if ($neighborName ne "null"){
                                $neighborUp = $vertices{$neighborName}[5][4];
                                if ($neighborUp eq "null"){
                                    print "ERROR : There is some bug in switch box definition !\n";
                                    exit(-1);
                                }
                            }

							# Via-to-via Spacing Rule
							$tmp_str = $tmp_str."+ M($neighborName)($neighborUp) ";
							$cnt_col++;
                        }
						if($prev_cnt_col == -1){
							$prev_cnt_col = $cnt_col;
							$tmp_out = $tmp_str;
						}
						else{
							if($prev_cnt_col == $cnt_col){
								$tmp_out = $tmp_out.$tmp_str;
							}
							else{
								print $out "M($vName)($vertices{$vName}[5][4]) ";
								print $out $tmp_out;
								print $out "<= 1\n";
								last;
							}
						}
                    }
                    # Stacked Via Rule
                    if ($metal != 1) {
                        if ( ($vertices{$vName}[5][4] eq "null") || ($vertices{$vName}[5][5] eq "null") ){
                            print "ERROR : There is some bug in switch box definition !\n";
                            exit(-1);
                        }
                        print $out "M($vName)($vertices{$vName}[5][4]) ";
                        print $out "+ M($vertices{$vName}[5][5])($vName) ";
                        print $out "<= 1\n";
                    }
                }
            }
        }
    }
    print $out "\n\n";
    print "has been written.\n";

}

print "a     11. Parallel Run Length Rule ";
print $out "\\ 11. Parallel Run Length Rule\n";
if ( $PRL_Parameter == 0 ){
    print "is disable....\n";
    print $out "\\ PRL is disable\n";
}
else{  # PRL Rule Enable /Disable
### Paralle Run-Length Rule to prevent from having too close metal tips.
### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    print $out "\\ 11-A. from Right Tip to Left Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 0) {  # M2
            for my $row (0 .. $numTrackH-1) {
                # skip the PRL rule related with power Rail.
                if ($row % ($trackEachRow + 1) == 0 ){
                    next;
                }
                for my $col (0 .. $numTrackV - 1) { # 
                    $vName = "m".$metal."r".$row."c".$col;
                    # F Direction Checking
                    my $vName_F = $vertices{$vName}[5][2];
                    if ( ($vName_F ne "null") && ($row % ($trackEachRow + 1) != 1) ) {
                        print $out "GR_V($vName) + ";
                        for my $prlIndex (0 .. $PRL_Parameter-1){  
                            print $out "GL_V($vName_F) ";
                            if ($prlIndex != ($PRL_Parameter-1)){
                                $vName_F = $vertices{$vName_F}[5][0];
                                if ($vName_F eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                    # B Direction Checking 
                    my $vName_B = $vertices{$vName}[5][3];
                    if ( ($vName_B ne "null") && ($row % ($trackEachRow + 1) != $trackEachRow)) {
                        print $out "GR_V($vName) + ";
                        for my $prlIndex (0 .. $PRL_Parameter-1){  
                            print $out "GL_V($vName_B) ";
                            if ($prlIndex != ($PRL_Parameter-1)){
                                $vName_B = $vertices{$vName_B}[5][0];
                                if ($vName_B eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                }
            }
        }
    }
    print $out "\n";


    ###### Skip to check exact adjacent GV variable, (From right to left is enough), 11-B is executed when PRL_Parameter > 1
    print $out "\\ 11-B. from Left Tip to Right Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 0) {  # M2
            for my $row (0 .. $numTrackH-1) {
                # skip the PRL rule related with power Rail.
                if ($row % ($trackEachRow + 1) == 0 ){
                    next;
                }
                for my $col (0 .. $numTrackV - 1) { # 
                    $vName = "m".$metal."r".$row."c".$col;
                    # FR Direction Checking
                    my $vName_FR = $vertices{$vName}[5][7];
                    if ( ($vName_FR ne "null") && ($row % ($trackEachRow + 1) != 1) && ($PRL_Parameter > 1) ) {
                        print $out "GL_V($vName) ";
                        for my $prlIndex (0 .. $PRL_Parameter-1){  
                            if ($prlIndex != ($PRL_Parameter-1)){
                                print $out "+ GR_V($vName_FR) ";
                                $vName_FR = $vertices{$vName_FR}[5][1];
                                if ($vName_FR eq "null"){
                                    last;
                                }
                            }
                        }
                        print $out "<= 1\n";
                    }
                    # BR Direction Checking 
                    my $vName_BR = $vertices{$vName}[5][9];
                    if ( ($vName_BR ne "null") && ($row % ($trackEachRow + 1) != $trackEachRow) && ($PRL_Parameter > 1) ) {
                        print $out "GL_V($vName) ";
                        for my $prlIndex (0 .. $PRL_Parameter-1){  
                            if ($prlIndex != ($PRL_Parameter-1)){
                                print $out "+ GR_V($vName_BR) ";
                                $vName_BR = $vertices{$vName_BR}[5][1];
                                if ($vName_BR eq "null"){
                                    last;
                                }
                            }
                        }
                        print $out "<= 1\n";
                    }
                }
            }
        }
    }
    print $out "\n";

### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
#
##### one Power Rail vertice has 2 times cost of other vertices. ($Double Power Rail)
#
    print $out "\\ 11-C. from Back Tip to Front Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 1) {
            for my $row (0 .. $numTrackH-1) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;
                    # Left Track Checking
                    my $vName_L = $vertices{$vName}[5][0];
                    if ($vName_L ne "null") {
                        print $out "GB_V($vName) + GF_V($vName_L)";
                        if ($PRL_Parameter > 1){
                            my $newRow = $row-1;
                            my $FlagforSecond = 0;
                            for my $prlIndex (0 .. $PRL_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }   
                                $FlagforSecond = 0;
                                $vName_L = $vertices{$vName_L}[5][2];
                                if ($vName_L eq "null"){
                                    last;
                                }
                                print $out " + GF_V($vName_L)";
                                $newRow--;
                            }
                        }
                        print $out " <= 1\n";
                    }
                    # Right Track Checking
                    my $vName_R = $vertices{$vName}[5][1];
                    if ($vName_R ne "null") {
                        print $out "GB_V($vName) + GF_V($vName_R)";
                        if ($PRL_Parameter > 1){
                            my $newRow = $row-1;
                            my $FlagforSecond = 0;
                            for my $prlIndex (0 .. $PRL_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }   
                                $FlagforSecond = 0;
                                $vName_R = $vertices{$vName_R}[5][2];
                                if ($vName_R eq "null"){
                                    last;
                                }
                                print $out " + GF_V($vName_R)";
                                $newRow--;
                            }
                        }
                        print $out " <= 1\n";
                    }

                }
            }
        }
    }
    print $out "\n";

    ###### Skip to check exact adjacent GV variable, (From right to left is enough), 11-B is executed when PRL_Parameter > 1
    print $out "\\ 11-D. from Front Tip to Back Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 1) {
            for my $row (0 .. $numTrackH-2) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;
                    # Left Track Checking
                    my $vName_L = $vertices{$vName}[5][0];
                    if (($vName_L ne "null") && ($PRL_Parameter > 1)) { 
                        my $newRow = $row+1;
                        if( ($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($PRL_Parameter == 2)) {
                            #### Nothing
                        }
                        else{
                            print $out "GF_V($vName)";
                            my $FlagforSecond = 0;
                            for my $prlIndex (0 .. $PRL_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }   
                                $FlagforSecond = 0;
                                $vName_L = $vertices{$vName_L}[5][3];
                                if ($vName_L eq "null"){
                                    last;
                                }
                                print $out " + GB_V($vName_L)";
                                $newRow++;
                            }
                            print $out " <= 1\n";
                        }
                    }

                    # Right Track Checking
                    my $vName_R = $vertices{$vName}[5][1];
                    if (($vName_R ne "null") && ($PRL_Parameter > 1)) { 
                        my $newRow = $row+1;
                        if( ($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($PRL_Parameter == 2)) {
                            #### Nothing
                        }
                        else{
                            print $out "GF_V($vName)";
                            my $FlagforSecond = 0;
                            for my $prlIndex (0 .. $PRL_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }   
                                $FlagforSecond = 0;
                                $vName_R = $vertices{$vName_R}[5][3];
                                if ($vName_R eq "null"){
                                    last;
                                }
                                print $out " + GB_V($vName_R)";
                                $newRow++;
                            }
                            print $out " <= 1\n";
                        }
                    }

                }
            }
        }
    }
    print $out "\n";
    print "has been written.\n";
}

print "a     12. Step Height Rule ";
print $out "\\ 12. Step Height Rule\n";
if ( $SHR_Parameter < 2 ){
    print "is disable.....\n";
    print $out "\\ SHR is disable\n";
}
else{

### Paralle Run-Length Rule to prevent from having too close metal tips.
### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent vertices]
### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    print $out "\\ 12-A. from Right Tip to Right Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 0) {  # M2
            for my $row (0 .. $numTrackH-1) {
                # skip the PRL rule related with power Rail.
                if ($row % ($trackEachRow + 1) == 0 ){
                    next;
                }
                for my $col (0 .. $numTrackV - 2) { # 
                    $vName = "m".$metal."r".$row."c".$col;
                    # FR Direction Checking
                    my $vName_FR = $vertices{$vName}[5][7];
                    if ( ($vName_FR ne "null") && ($row % ($trackEachRow + 1) != 1) ) {
                        print $out "GR_V($vName) + ";
                        for my $shrIndex (0 .. $SHR_Parameter-2){  
                            print $out "GR_V($vName_FR) ";
                            if ($shrIndex != ($SHR_Parameter-2)){
                                $vName_FR = $vertices{$vName_FR}[5][1];
                                if ($vName_FR eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                    # BR Direction Checking 
                    my $vName_BR = $vertices{$vName}[5][9];
                    if ( ($vName_BR ne "null") && ($row % ($trackEachRow + 1) != $trackEachRow)) {
                        print $out "GR_V($vName) + ";
                        for my $shrIndex (0 .. $SHR_Parameter-2){  
                            print $out "GR_V($vName_BR) ";
                            if ($shrIndex != ($SHR_Parameter-2)){
                                $vName_BR = $vertices{$vName_BR}[5][1];
                                if ($vName_BR eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                }
            }
        }
    }
    print $out "\n";

    print $out "\\ 12-B. from Left Tip to Left Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 0) {  # M2
            for my $row (0 .. $numTrackH-1) {
                # skip the PRL rule related with power Rail.
                if ($row % ($trackEachRow + 1) == 0 ){
                    next;
                }
                for my $col (1 .. $numTrackV - 1) { # 
                    $vName = "m".$metal."r".$row."c".$col;
                    # FL Direction Checking
                    my $vName_FL = $vertices{$vName}[5][6];
                    if ( ($vName_FL ne "null") && ($row % ($trackEachRow + 1) != 1) ) {
                        print $out "GL_V($vName) + ";
                        for my $shrIndex (0 .. $SHR_Parameter-2){  
                            print $out "GL_V($vName_FL) ";
                            if ($shrIndex != ($SHR_Parameter-2)){
                                $vName_FL = $vertices{$vName_FL}[5][0];
                                if ($vName_FL eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                    # BL Direction Checking 
                    my $vName_BL = $vertices{$vName}[5][8];
                    if ( ($vName_BL ne "null") && ($row % ($trackEachRow + 1) != $trackEachRow)) {
                        print $out "GL_V($vName) + ";
                        for my $shrIndex (0 .. $SHR_Parameter-2){  
                            print $out "GL_V($vName_BL) ";
                            if ($shrIndex != ($SHR_Parameter-2)){
                                $vName_BL = $vertices{$vName_BL}[5][0];
                                if ($vName_BL eq "null"){
                                    last;
                                }
                                print $out "+ ";
                            }
                        }
                        print $out "<= 1\n";
                    }
                }
            }
        }
    }
    print $out "\n";

    ###### Skip to check exact adjacent GV variable, (From right to left is enough), 11-B is executed when PRL_Parameter > 1
    print $out "\\ 12-C. from Back Tip to Back Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 1) {
            for my $row (0 .. $numTrackH-2) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;

                    # Left-Back Track Checking
                    my $vName_LB = $vertices{$vName}[5][8];
                    if (($vName_LB ne "null")) { 
                        my $newRow = $row + 1;
                        if( ($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($SHR_Parameter == 2)) {
                            #### Nothing
                        }
                        else{
                            print $out "GB_V($vName)";
                            my $FlagforSecond = 0;
                            for my $shrIndex (0 .. $SHR_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }   
                                $FlagforSecond = 0;
                                print $out " + GB_V($vName_LB)";
                                $vName_LB = $vertices{$vName_LB}[5][3];

                                if ($vName_LB eq "null"){
                                    last;
                                }
                                $newRow++;
                            }
                            print $out " <= 1\n";
                        }

                    }

                    # Right-Back Track Checking
                    my $vName_RB = $vertices{$vName}[5][9];
                    if (($vName_RB ne "null")) { 
                        my $newRow = $row + 1;
                        if( ($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($SHR_Parameter == 2)) {
                            #### Nothing
                        }
                        else{
                            print $out "GB_V($vName)";
                            my $FlagforSecond = 0;
                            for my $shrIndex (0 .. $SHR_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }   
                                $FlagforSecond = 0;
                                print $out " + GB_V($vName_RB)";
                                $vName_RB = $vertices{$vName_RB}[5][3];
                                if ($vName_RB eq "null"){
                                    last;
                                }
                                $newRow++;
                            }
                            print $out " <= 1\n";
                        }
                    }

                }
            }
        }
    }
    print $out "\n";

    print $out "\\ 12-D. from Front Tip to Front Tips for each vertex\n";
    for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
        if ($metal % 2 == 1) {
            for my $row (1 .. $numTrackH-1) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;

                    # Left-Front Direction
                    my $vName_LF = $vertices{$vName}[5][6];
                    if (($vName_LF ne "null")) {
                        my $newRow = $row - 1;
                        if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($SHR_Parameter == 2)){ # Skip the BR Direction
                            ### Nothing
                        }
                        else{
                            print $out "GF_V($vName)"; 
                            my $FlagforSecond = 0;
                            for my $shrIndex (0 .. $SHR_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }
                                $FlagforSecond = 0;
                                print $out " + GF_V($vName_LF)";
                                $vName_LF = $vertices{$vName_LF}[5][2];
                                if (($vName_LF eq "null")){
                                    last;
                                }
                                $newRow--;
                            }
                            print $out " <= 1\n";
                        }
                    }

                    # Right-Front Direction
                    my $vName_RF = $vertices{$vName}[5][7];
                    if (($vName_RF ne "null")) {
                        my $newRow = $row - 1;
                        if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($SHR_Parameter == 2)){ # Skip the BR Direction
                            ### Nothing
                        }
                        else{
                            print $out "GF_V($vName)"; 
                            my $FlagforSecond = 0;
                            for my $shrIndex (0 .. $SHR_Parameter-2){
                                if (($DoublePowerRail == 1) && ($newRow % ($trackEachRow + 1) == 0) && ($FlagforSecond == 0)){
                                    $FlagforSecond = 1;
                                    next;
                                }
                                $FlagforSecond = 0;
                                print $out " + GF_V($vName_RF)";
                                $vName_RF = $vertices{$vName_RF}[5][2];
                                if (($vName_RF eq "null")){
                                    last;
                                }
                                $newRow--;
                            }
                            print $out " <= 1\n";
                        }
                    }

                }
            }
        }
    }
    print $out "\n\n";

    print "has been written.\n";

}

print $out "\\\\\\ End of Constraints \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\n\n\n\n";

### CPLEX ILP FORMULATION VARIABLE Declaration
print $out "\\\\\\ Definitions of Variables \\\\\\\\\\\\\\\\\\\n\n";

### SOURCE and SINK DEFINITION per NET per COMMODITY and per VERTEX (including supernodes, i.e., pins)
print "a     10. Variable conditions, e.g., bound and binary, ";
print $out "\\ 10. Variable conditions, e.g., bound and binary. \n\n";
print $out "Bounds\n\n";
print $out "\\ Following variables are bounded.\n";

### Bounds for given routing results
print $out "\n\n";
print $out "\\ Bounds for given routing results(Obstacles & SON Node)\n\n";

my %h_obs = ();
my %h_son = ();
my %h_boundary = ();

my %h_nets_commodity = ();
if(scalar(@metal)>0){
	for(my $i=0; $i<=$#metal; $i++){
		# obstacle metal - set bounds for metal variables
		if(!exists($h_nets_id{$metal[$i][0]})){
			my $vName1 = "";
			my $vName2 = "";
			if($no_vobs == 0){
				$vName1 = "m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+1);
				$vName2 = "m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+1);
			}
			else{
				$vName1 = "m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$no_vobs);
				$vName2 = "m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$no_vobs);
			}
			print $out "M($vName1)($vName2) = 1\n";
			$h_obs{"M($vName1)($vName2)"} = 1;
			for my $netIndex (0 .. $#nets) {
				print $out "N$nets[$netIndex][1]_";
				print $out "E($vName1)($vName2) = 0\n";
				print $out "N$nets[$netIndex][1]_";
				print $out "E($vName2)($vName1) = 0\n";
				if($metal[$i][1]%2==0){
					## prevent routing between obstacle and adjacent normal vertices
					# Left
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][0] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][0]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][0])($vName1) = 0\n";
						}
					}
					# Right
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][1] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][1]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][1])($vName1) = 0\n";
						}
					}
					# Up
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][4] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][4]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][4])($vName1) = 0\n";
						}
					}
					# Down
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][5] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][5]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][5])($vName1) = 0\n";
						}
					}
				}
				else{
					# Front
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][2] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][2]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][2])($vName1) = 0\n";
						}
					}
					# Back
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][3] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][3]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][3])($vName1) = 0\n";
						}
					}
					# Up
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][4] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][4]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][4])($vName1) = 0\n";
						}
					}
					# Down
					if(!exists($h_obs_extnode{$vName1})){
						if($vertices{$vName1}[5][5] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName1)($vertices{$vName1}[5][5]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName1}[5][5])($vName1) = 0\n";
						}
					}
				}
				if($metal[$i][2]%2==0){
					## prevent routing between obstacle and adjacent normal vertices
					# Left
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][0] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][0]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][0])($vName2) = 0\n";
						}
					}
					# Right
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][1] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][1]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][1])($vName2) = 0\n";
						}
					}
					# Up
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][4] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][4]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][4])($vName2) = 0\n";
						}
					}
					# Down
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][5] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][5]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][5])($vName2) = 0\n";
						}
					}
				}
				else{
					# Front
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][2] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][2]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][2])($vName2) = 0\n";
						}
					}
					# Back
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][3] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][3]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][3])($vName2) = 0\n";
						}
					}
					# Up
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][4] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][4]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][4])($vName2) = 0\n";
						}
					}
					# Down
					if(!exists($h_obs_extnode{$vName2})){
						if($vertices{$vName2}[5][5] ne "null"){
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vName2)($vertices{$vName2}[5][5]) = 0\n";
							print $out "N$nets[$netIndex][1]_";
							print $out "E($vertices{$vName2}[5][5])($vName2) = 0\n";
						}
					}
				}
				for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
					print $out "N$nets[$netIndex][1]_";
					print $out "C$commodityIndex\_";
					print $out "E($vName1)($vName2) = 0\n";
					print $out "N$nets[$netIndex][1]_";
					print $out "C$commodityIndex\_";
					print $out "E($vName2)($vName1) = 0\n";
					if($metal[$i][1]%2==0){
						## prevent routing between obstacle and adjacent normal vertices
						# Left
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][0] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][0]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][0])($vName1) = 0\n";
							}
						}
						# Right
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][1] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][1]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][1])($vName1) = 0\n";
							}
						}
						# Up
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][4] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][4]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][4])($vName1) = 0\n";
							}
						}
						# Down
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][5] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][5]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][5])($vName1) = 0\n";
							}
						}
					}
					else{
						# Front
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][2] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][2]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][2])($vName1) = 0\n";
							}
						}
						# Back
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][3] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][3]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][3])($vName1) = 0\n";
							}
						}
						# Up
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][4] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][4]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][4])($vName1) = 0\n";
							}
						}
						# Down
						if(!exists($h_obs_extnode{$vName1})){
							if($vertices{$vName1}[5][5] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName1)($vertices{$vName1}[5][5]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName1}[5][5])($vName1) = 0\n";
							}
						}
					}
					if($metal[$i][2]%2==0){
						## prevent routing between obstacle and adjacent normal vertices
						# Left
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][0] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][0]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][0])($vName2) = 0\n";
							}
						}
						# Right
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][1] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][1]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][1])($vName2) = 0\n";
							}
						}
						# Up
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][4] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][4]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][4])($vName2) = 0\n";
							}
						}
						# Down
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][5] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][5]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][5])($vName2) = 0\n";
							}
						}
					}
					else{
						# Front
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][2] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][2]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][2])($vName2) = 0\n";
							}
						}
						# Back
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][3] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][3]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][3])($vName2) = 0\n";
							}
						}
						# Up
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][4] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][4]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][4])($vName2) = 0\n";
							}
						}
						# Down
						if(!exists($h_obs_extnode{$vName2})){
							if($vertices{$vName2}[5][5] ne "null"){
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vName2)($vertices{$vName2}[5][5]) = 0\n";
								print $out "N$nets[$netIndex][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($vertices{$vName2}[5][5])($vName2) = 0\n";
							}
						}
					}
				}
			}
		}
		else{ 
			#external commodity - set bounds for SON Node
			my $tmp_netid = $h_nets_id{$metal[$i][0]};
			my $tmp_idx_net = $h_nets{$tmp_netid};

			for my $commodityIndex (0 .. $nets[$tmp_idx_net][4]-1) {
				if($nets[$tmp_idx_net][5][$commodityIndex] eq "pinSON"){
					if(!exists($h_nets_commodity{$tmp_netid."|".$commodityIndex})){
						my $offset = 0;
						if($no_vobs == 0){
							$offset = 1;
						}
						else{
							$offset = $no_vobs;
						}
						if($metal[$i][1] == $metal[$i][2] && $metal[$i][1]%2 == 0){
							if ($metal[$i][5] == -1){
								$h_nets_commodity{$tmp_netid."|".$commodityIndex} = 1;
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")($keySON) = 1\n";
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($keySON)(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).") = 0\n";
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")($keySON)"} = 1;
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E($keySON)(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;

								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset+1).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset+1).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset+1).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset+1).")"} = 1;
								$h_boundary{"M(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset+1).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"M(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset+1).")"} = 1;
								last;
							}
							elsif ($metal[$i][6] == $numTrackV - 2*$no_vobs){
								$h_nets_commodity{$tmp_netid."|".$commodityIndex} = 1;
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")($keySON) = 1\n";
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($keySON)(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).") = 0\n";
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")($keySON)"} = 1;
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E($keySON)(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")"} = 1;

								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset-1).")(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset-1).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset-1).")(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset-1).")"} = 1;
								$h_boundary{"M(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset-1).")(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"M(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset-1).")"} = 1;
								last;
							}
						}
						elsif($metal[$i][1] == $metal[$i][2] && $metal[$i][1]%2 == 1){
							if($metal[$i][3] == 0){
								$h_nets_commodity{$tmp_netid."|".$commodityIndex} = 1;
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")($keySON) = 1\n";
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($keySON)(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).") = 0\n";
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")($keySON)"} = 1;
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E($keySON)(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;

								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][1]r".($metal[$i][3]+1)."c".($metal[$i][5]+$offset).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][1]r".($metal[$i][3])."c".($metal[$i][5]+$offset).")(m$metal[$i][1]r".($metal[$i][3]+1)."c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][1]r".($metal[$i][3]+1)."c".($metal[$i][5]+$offset).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][1]r".($metal[$i][3])."c".($metal[$i][5]+$offset).")(m$metal[$i][1]r".($metal[$i][3]+1)."c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"M(m$metal[$i][1]r".($metal[$i][3]+1)."c".($metal[$i][5]+$offset).")(m$metal[$i][1]r$metal[$i][3]c".($metal[$i][5]+$offset).")"} = 1;
								$h_boundary{"M(m$metal[$i][1]r".($metal[$i][3])."c".($metal[$i][5]+$offset).")(m$metal[$i][1]r".($metal[$i][3]+1)."c".($metal[$i][5]+$offset).")"} = 1;
								last;
							}
							elsif($metal[$i][4] == $numTrackH - 1){
								$h_nets_commodity{$tmp_netid."|".$commodityIndex} = 1;
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")($keySON) = 1\n";
								print $out "N$nets[$tmp_idx_net][1]_";
								print $out "C$commodityIndex\_";
								print $out "E($keySON)(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).") = 0\n";
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")($keySON)"} = 1;
								$h_son{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E($keySON)(m$metal[$i][2]r$metal[$i][4]c".($metal[$i][6]+$offset).")"} = 1;

								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][2]r".($metal[$i][4]-1)."c".($metal[$i][6]+$offset).")(m$metal[$i][2]r".($metal[$i][4])."c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_C$commodityIndex\_E(m$metal[$i][2]r".($metal[$i][4])."c".($metal[$i][6]+$offset).")(m$metal[$i][2]r".($metal[$i][4]-1)."c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][2]r".($metal[$i][4]-1)."c".($metal[$i][6]+$offset).")(m$metal[$i][2]r".($metal[$i][4])."c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"N$nets[$tmp_idx_net][1]_E(m$metal[$i][2]r".($metal[$i][4])."c".($metal[$i][6]+$offset).")(m$metal[$i][2]r".($metal[$i][4]-1)."c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"M(m$metal[$i][2]r".($metal[$i][4]-1)."c".($metal[$i][6]+$offset).")(m$metal[$i][2]r".($metal[$i][4])."c".($metal[$i][6]+$offset).")"} = 1;
								$h_boundary{"M(m$metal[$i][2]r".($metal[$i][4])."c".($metal[$i][6]+$offset).")(m$metal[$i][2]r".($metal[$i][4]-1)."c".($metal[$i][6]+$offset).")"} = 1;
								last;
							}
						}
					}
				}
			}
		}
	}
}
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $pinIndex (0 .. $#pins) {
            $vName = $pins[$pinIndex][0];
			if($vName eq $keySON){
				for my $i (0 .. $#{$vedge_in{$vName}}){ # sink
					if(!exists($h_son{"N$nets[$netIndex][1]\_C$commodityIndex\_E($virtualEdges[$vedge_in{$vName}[$i]][1])($vName)"})){
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($virtualEdges[$vedge_in{$vName}[$i]][1])($vName) = 0\n";
					}
					if(!exists($h_son{"N$nets[$netIndex][1]\_C$commodityIndex\_E($vName)($virtualEdges[$vedge_in{$vName}[$i]][1])"})){
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($vName)($virtualEdges[$vedge_in{$vName}[$i]][1]) = 0\n";
					}
				}
				for my $i (0 .. $#{$vedge_out{$vName}}){ # source
					if(!exists($h_son{"N$nets[$netIndex][1]\_C$commodityIndex\_E($vName)($virtualEdges[$vedge_out{$vName}[$i]][2])"})){
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($vName)($virtualEdges[$vedge_out{$vName}[$i]][2]) = 0\n";
					}
					if(!exists($h_son{"N$nets[$netIndex][1]\_C$commodityIndex\_E($virtualEdges[$vedge_out{$vName}[$i]][2])($vName)"})){
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($virtualEdges[$vedge_out{$vName}[$i]][2])($vName) = 0\n";
					}
				}
			}
        }
        print $out "\n";
    }
}
print $out "\n";
# Disable Routing for obstacle area
print $out "\n\\ prevent routing via obstacle area.\n";
if($no_vobs == 0){
	# disable each right/leftmost column
	for my $udeIndex (0 .. $#udEdges) {
		my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
		my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
		my $fromCol = (split /[a-z]/, $udEdges[$udeIndex][1])[3]; # 1:metal 2:row 3:col
		my $toCol   = (split /[a-z]/, $udEdges[$udeIndex][2])[3];
		if (($fromCol == $toCol) && ($fromCol == 0 || $fromCol == $numTrackV - 1)) {
			print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
			if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
				print $out "M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
			}
		}
	}
	print $out "\n";
	for my $netIndex (0 .. $#nets) {
		for my $udeIndex (0 .. $#udEdges) {
			my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
			my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
			my $fromCol = (split /[a-z]/, $udEdges[$udeIndex][1])[3]; # 1:metal 2:row 3:col
			my $toCol   = (split /[a-z]/, $udEdges[$udeIndex][2])[3];
			if (($fromCol == $toCol) && ($fromCol == 0 || $fromCol == $numTrackV - 1)) {
				if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
				}
			}
		}
		print $out "\n";
	}
	for my $netIndex (0 .. $#nets) {
		for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
			for my $udeIndex (0 .. $#udEdges) {
				my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
				my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
				my $fromCol = (split /[a-z]/, $udEdges[$udeIndex][1])[3]; # 1:metal 2:row 3:col
				my $toCol   = (split /[a-z]/, $udEdges[$udeIndex][2])[3];
				if (($fromCol == $toCol) && ($fromCol == 0 || $fromCol == $numTrackV - 1)) {
					print $out "N$nets[$netIndex][1]\_";
					print $out "C$commodityIndex\_";
					print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "C$commodityIndex\_";
					print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
				}
			}
			print $out "\n";
		}
	}
	print $out "\n";
}
else{
	# disable each right/leftmost column
	for my $udeIndex (0 .. $#udEdges) {
		my $fromM   = (split /[a-z]/, $udEdges[$udeIndex][1])[1]; # 1:metal 2:row 3:col
		my $toM     = (split /[a-z]/, $udEdges[$udeIndex][2])[1];
		my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
		my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
		my $fromCol = (split /[a-z]/, $udEdges[$udeIndex][1])[3]; # 1:metal 2:row 3:col
		my $toCol   = (split /[a-z]/, $udEdges[$udeIndex][2])[3];
		if (($fromCol == $toCol) && ($fromCol <= $no_vobs - 1 || $fromCol >= $numTrackV - ($no_vobs - 1) - 1)) {
			print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
			if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
				print $out "M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
			}
		}
		elsif (($fromM != $toM) && ($fromRow == $toRow) && ($toCol <= $no_vobs - 1 || $fromCol >= $numTrackV - ($no_vobs - 1) - 1)) {
			print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
			if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
				print $out "M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
			}
		}
		elsif (($fromM == $toM) && ($fromRow == $toRow) && ($toCol <= $no_vobs || $fromCol >= $numTrackV - $no_vobs - 1)) {
			if(!exists($h_boundary{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
				print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
				if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
					print $out "M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
				}
			}
		}
	}
	print $out "\n";
	for my $netIndex (0 .. $#nets) {
		for my $udeIndex (0 .. $#udEdges) {
			my $fromM   = (split /[a-z]/, $udEdges[$udeIndex][1])[1]; # 1:metal 2:row 3:col
			my $toM     = (split /[a-z]/, $udEdges[$udeIndex][2])[1];
			my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
			my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
			my $fromCol = (split /[a-z]/, $udEdges[$udeIndex][1])[3]; # 1:metal 2:row 3:col
			my $toCol   = (split /[a-z]/, $udEdges[$udeIndex][2])[3];
			if (($fromCol == $toCol) && ($fromCol <= $no_vobs - 1 || $fromCol >= $numTrackV - ($no_vobs - 1) - 1)) {
				if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
				}
			}
			elsif (($fromM != $toM) && ($fromRow == $toRow) && ($toCol <= $no_vobs - 1 || $fromCol >= $numTrackV - ($no_vobs - 1) - 1)) {
				if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
				}
			}
			elsif (($fromM == $toM) && ($fromRow == $toRow) && ($toCol <= $no_vobs || $fromCol >= $numTrackV - $no_vobs - 1)) {
				if(!exists($h_obs{"M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
					if(!exists($h_boundary{"N$nets[$netIndex][1]\_E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
						print $out "N$nets[$netIndex][1]\_";
						print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
						print $out "N$nets[$netIndex][1]\_";
						print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
					}
				}
			}
		}
		print $out "\n";
	}
	for my $netIndex (0 .. $#nets) {
		for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
			for my $udeIndex (0 .. $#udEdges) {
				my $fromM   = (split /[a-z]/, $udEdges[$udeIndex][1])[1]; # 1:metal 2:row 3:col
				my $toM     = (split /[a-z]/, $udEdges[$udeIndex][2])[1];
				my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
				my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
				my $fromCol = (split /[a-z]/, $udEdges[$udeIndex][1])[3]; # 1:metal 2:row 3:col
				my $toCol   = (split /[a-z]/, $udEdges[$udeIndex][2])[3];
				if (($fromCol == $toCol) && ($fromCol <= $no_vobs - 1 || $fromCol >= $numTrackV - ($no_vobs - 1) - 1)) {
					print $out "N$nets[$netIndex][1]\_";
					print $out "C$commodityIndex\_";
					print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "C$commodityIndex\_";
					print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
				}
				elsif (($fromM != $toM) && ($fromRow == $toRow) && ($toCol <= $no_vobs - 1 || $fromCol >= $numTrackV - ($no_vobs - 1) - 1)) {
					print $out "N$nets[$netIndex][1]\_";
					print $out "C$commodityIndex\_";
					print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "C$commodityIndex\_";
					print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
				}
				elsif (($fromM == $toM) && ($fromRow == $toRow) && ($toCol <= $no_vobs || $fromCol >= $numTrackV - $no_vobs - 1)) {
					if(!exists($h_boundary{"N$nets[$netIndex][1]\_C$commodityIndex\_E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])"})){
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
						print $out "N$nets[$netIndex][1]\_";
						print $out "C$commodityIndex\_";
						print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
					}
				}
			}
			print $out "\n";
		}
	}
	print $out "\n";
}

my @arr_local = ();
my %h_new_dir = ();
print $out "\\ Source and Sink Definitions per each Commodity in each Net for every Vertex.\n\n";
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $metal (1 .. $numMetalLayer) {   
            for my $row (0 .. $numTrackH-1) {
                for my $col (0 .. $numTrackV-1) {
                    $vName = "m".$metal."r".$row."c".$col;
                    #@net = ($netName, $netID, $N_pinNets, $source_ofNet, $numSinks, [@sinks_inNet], [@pins_inNet]);
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "C$commodityIndex\_";
                    print $out "V($vName) = 0\n";
                }
            }
        }
        for my $pin (0 .. $#pins) {
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";

			if ($nets[$netIndex][3] eq $pins[$pin][0]) { # then source
				print $out "V($pins[$pin][0]) = 1\n";
			}
			elsif ($nets[$netIndex][5][$commodityIndex] eq $pins[$pin][0]) { # then sink
				print $out "V($pins[$pin][0]) = -1\n";
			}
			else {
				print $out "V($pins[$pin][0]) = 0\n";
			}
        }
        print $out "\n";
    }
}
print $out "\n";

### VIRTUAL EDGES having definitely infeasible features, e.g., from sink to vertex, and from vertex to source.
### VIRTUAL_EDGE [index] [Origin] [Destination] [Cost=0]
#@net = ($netName, $netID, $N_pinNets, $source_ofNet, $numSinks, [@sinks_inNet], [@pins_inNet]);
print $out "\\ Infeasible virtual edges to Source and from Sink.\n\n";
for my $netIndex (0 .. $#nets) {
    for my $vEdgeIndex (0 .. $#virtualEdges) {
        if ($virtualEdges[$vEdgeIndex][1] =~ /^pin/) { # source 
            print $out "N$nets[$netIndex][1]\_E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) = 0\n";
        }
        elsif ($virtualEdges[$vEdgeIndex][2] =~ /^pin/) { # sink
            print $out "N$nets[$netIndex][1]\_E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) = 0\n";
        }
        elsif ($virtualEdges[$vEdgeIndex][2] eq $keySON) { # SON  
            print $out "N$nets[$netIndex][1]\_E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) = 0\n";
        }
    }
    print $out "\n";
}
print $out "\n";

print $out "\\ Infeasible virtual commodity flows to Source and from Sink.\n\n";
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $vEdgeIndex (0 .. $#virtualEdges) {
            if ($virtualEdges[$vEdgeIndex][1] =~ /^pin/) { # source
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) = 0\n";
            }
            elsif ($virtualEdges[$vEdgeIndex][2] =~ /^pin/) { # sink
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) = 0\n";
            }
            elsif ($virtualEdges[$vEdgeIndex][2] eq $keySON) { # SON
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($virtualEdges[$vEdgeIndex][2])($virtualEdges[$vEdgeIndex][1]) = 0\n";
            }
        }
        print $out "\n";
    }
}
print $out "\n";

print $out "\\ Infeasible virtual edges which net doesn't contain the pin.\n\n";
for my $netIndex (0 .. $#nets) {
    for my $vEdgeIndex (0 .. $#virtualEdges) {
        if ($virtualEdges[$vEdgeIndex][1] =~ /^pin/) { # source
            my $netInfo;
            for my $pinID (0 .. $#pins){ 
                if ($pins[$pinID][0] eq $virtualEdges[$vEdgeIndex][1]){
                    $netInfo = $pins[$pinID][1];
                    last;
                }
            }
            if( $nets[$netIndex][0] eq $netInfo){
                next;
            }
            else{
                print $out "N$nets[$netIndex][1]\_E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) = 0\n";
            }
        }
        elsif ($virtualEdges[$vEdgeIndex][2] =~ /^pin/) { # sink / pinSON case should be processed...!!!!
            if ($virtualEdges[$vEdgeIndex][2] eq $keySON) { # SON
                my $outerFlag = 0;
                for my $outerIndex (0 .. $#outerPins){
                    if ( $outerPins[$outerIndex][1] eq $nets[$netIndex][0] ){
                        $outerFlag = 1;
                        last;
                    }   
                }
                
                if ($outerFlag == 1){
                    next;
                }
                else{
                    print $out "N$nets[$netIndex][1]\_E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) = 0\n";
                }
            }
            else{
                my $netInfo;
                for my $pinID (0 .. $#pins){ 
                    if ($pins[$pinID][0] eq $virtualEdges[$vEdgeIndex][2]){
                        $netInfo = $pins[$pinID][1];
                        last;
                    }
                }
                if( $nets[$netIndex][0] eq $netInfo){
                    next;
                }
                else{
                    print $out "N$nets[$netIndex][1]\_E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) = 0\n";
                }
            }
        }
    }
    print $out "\n";
}
print $out "\n";
#####################################

print $out "\\ Infeasible virtual commodity which net doesn't contain the pin.\n\n";
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $vEdgeIndex (0 .. $#virtualEdges) {
            if ($virtualEdges[$vEdgeIndex][1] =~ /^pin/) { # source
                my $netInfo;
                for my $pinID (0 .. $#pins){
                    if ($pins[$pinID][0] eq $virtualEdges[$vEdgeIndex][1]){
                        $netInfo = $pins[$pinID][1];
                        last;
                    }
                }
                if( $nets[$netIndex][0] eq $netInfo){
                    next;
                }
                else{
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "C$commodityIndex\_";
                    print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) = 0\n";
                }
            }
            elsif ($virtualEdges[$vEdgeIndex][2] =~ /^pin/) { # sink
                if ($virtualEdges[$vEdgeIndex][2] eq $keySON){ # SON
                    my $outerFlag = 0;
                    for my $outerIndex (0 .. $#outerPins){
                        if ( $outerPins[$outerIndex][1] eq $nets[$netIndex][0] ){
                            $outerFlag = 1;
                            last;
                        }   
                    }
                    
                    if ($outerFlag == 1){
                        next;
                    }
                    else{
                        print $out "N$nets[$netIndex][1]\_";
                        print $out "C$commodityIndex\_";
                        print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) = 0\n";
                    }
                }
                else{ 
                    my $netInfo;
                    for my $pinID (0 .. $#pins){ 
                        if ($pins[$pinID][0] eq $virtualEdges[$vEdgeIndex][2]){
                            $netInfo = $pins[$pinID][1];
                            last;
                        }
                    }
                    if( $nets[$netIndex][0] eq $netInfo){
                        next;
                    }
                    else{
                        print $out "N$nets[$netIndex][1]\_";
                        print $out "C$commodityIndex\_";
                        print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2]) = 0\n";
                    }
                }
            }
        }
        print $out "\n";
    }
}
print $out "\n";
### Set M1 segments on pins.
#@pin = ($pinName, $pin_netID, $pinIO, $pinLength, $pinXpos, [@pinYpos]);
### Collect M1 Vertices and Edges in Inner Pins
### Undirected Edges in Pins: [0: pinName] [1: term1] [2: term2]
my @udEdgesInPins = ();
print $out "\\ Set M1 segments on pins, which are given by input layout.\n\n";
for my $pinIndex (0 .. $#pins) {
    if ($pins[$pinIndex][3] != -1) { # IF a pin is not outer pin
        for my $pinRowIndex (0 .. $pins[$pinIndex][3]-2) {
            my $tempRow = $pins[$pinIndex][5][$pinRowIndex];
            my $tempCol = $pins[$pinIndex][4];
            my $vName1 = "m1r".$tempRow."c".$tempCol;
            my $tempRow = $pins[$pinIndex][5][$pinRowIndex]+1;
            my $vName2 = "m1r".$tempRow."c".$tempCol;
            push @udEdgesInPins, [$pins[$pinIndex][0], $vName1, $vName2];
        }
    }
}
### UNDIRECTED_EDGE [index] [Term1] [Term2] [Cost]
for my $udeIndex (0 .. $#udEdges) {
    my $vName1 = $udEdges[$udeIndex][1];
    my $vName2 = $udEdges[$udeIndex][2];
    for my $epIndex (0 .. $#udEdgesInPins) {
        if (($vName1 eq $udEdgesInPins[$epIndex][1]) && ($vName2 eq $udEdgesInPins[$epIndex][2])) {
            print $out "M($vName1)($vName2) = 1\n";
        }
    }
}
print $out "\n\n";
print $out "\\ Unset Unused M1 segments out of pins, which are given by input layout.\n\n";
for my $udeIndex (0 .. $#udEdges) {
    my $vName1 = $udEdges[$udeIndex][1];
    my $vName2 = $udEdges[$udeIndex][2];
    my $onPin = 0;
    if (($vName1 =~ /m1r/) && ($vName2 =~ /m1r/)) {
        for my $epIndex (0 .. $#udEdgesInPins) {
            if (($vName1 eq $udEdgesInPins[$epIndex][1]) && ($vName2 eq $udEdgesInPins[$epIndex][2])) {
                $onPin = 1;
            }
        }
        if ($onPin == 0) {
			if(!exists($h_obs{"M($vName1)($vName2)"})){
				print $out "M($vName1)($vName2) = 0\n";
			}
            print $out "W($vName1)($vName2) = 0\n";
            for my $netIndex (0 .. $#nets) {
				if(!exists($h_obs{"M($vName1)($vName2)"})){
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($vName1)($vName2) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($vName2)($vName1) = 0\n";
				}
                for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "C$commodityIndex\_";
                    print $out "E($vName1)($vName2) = 0\n";
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "C$commodityIndex\_";
                    print $out "E($vName2)($vName1) = 0\n";
                }
            }
        }
    }
    elsif (($vName1 =~ /m1r/) && ($vName2 =~ /m2r/)) {
        for my $epIndex (0 .. $#udEdgesInPins) {
            if (($vName1 eq $udEdgesInPins[$epIndex][1]) || ($vName1 eq $udEdgesInPins[$epIndex][2])) {
                $onPin = 1;
            }
        }
        if ($onPin == 0) {
			if(!exists($h_obs{"M($vName1)($vName2)"})){
				print $out "M($vName1)($vName2) = 0\n";
			}
            print $out "W($vName1)($vName2) = 0\n";
            for my $netIndex (0 .. $#nets) {
				if(!exists($h_obs{"M($vName1)($vName2)"})){
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($vName1)($vName2) = 0\n";
					print $out "N$nets[$netIndex][1]\_";
					print $out "E($vName2)($vName1) = 0\n";
				}
                for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "C$commodityIndex\_";
                    print $out "E($vName1)($vName2) = 0\n";
                    print $out "N$nets[$netIndex][1]\_";
                    print $out "C$commodityIndex\_";
                    print $out "E($vName2)($vName1) = 0\n";
                }
            }
        }
    }
    else {
        next;
    }
}
print $out "\n\n";

# there are no adjacent vertices in L, R, F, B directions.
# 0: Fixed (Set by Assignment), 1: Extensible (Go to Binaries Definition) [2018-07-06]

if ($BoundaryCondition == 0){
    print $out "\\ There are no adjacent vertices in L, R, F, B directions.\n\n";
    for my $leftVertex (0 .. $#leftCorners) {
        my $metal = (split /[a-z]/, $leftCorners[$leftVertex])[1];
        if ($metal % 2 == 0) {
            print $out "M(LeftEnd)($leftCorners[$leftVertex]) = 0\n";
        }
    }
    for my $rightVertex (0 .. $#rightCorners) {
        my $metal = (split /[a-z]/, $rightCorners[$rightVertex])[1];
        if ($metal % 2 == 0) {
            print $out "M($rightCorners[$rightVertex])(RightEnd) = 0\n";
        }
    }
    for my $frontVertex (0 .. $#frontCorners) {
        my $metal = (split /[a-z]/, $frontCorners[$frontVertex])[1];
        if ($metal % 2 == 1) {
            print $out "M(FrontEnd)($frontCorners[$frontVertex]) = 0\n";
        }
    }
    for my $backVertex (0 .. $#backCorners) {
        my $metal = (split /[a-z]/, $backCorners[$backVertex])[1];
        if ($metal % 2 == 1) {
            print $out "M($backCorners[$backVertex])(BackEnd) = 0\n";
        }
    }
}
print $out "\n\n";

### Preventing from having horizontal metal segments on power grids.
### UNDIRECTED_EDGE [index] [Term1] [Term2] [Cost]
print $out "\\ On power lines, horizontal metal segments and vias are not allowed.\n\n";
for my $udeIndex (0 .. $#udEdges) {
    my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
    my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
    if (($fromRow % ($trackEachRow + 1) == 0) && ($fromRow == $toRow)) { # on power grid
        print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
        print $out "M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
    }
}
print $out "\n";
for my $netIndex (0 .. $#nets) {
    for my $udeIndex (0 .. $#udEdges) {
        my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
        my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
        if (($fromRow % ($trackEachRow + 1) == 0) && ($fromRow == $toRow)) { # on power grid
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
        }
    }
    print $out "\n";
}
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $udeIndex (0 .. $#udEdges) {
            my $fromRow = (split /[a-z]/, $udEdges[$udeIndex][1])[2]; # 1:metal 2:row 3:col
            my $toRow   = (split /[a-z]/, $udEdges[$udeIndex][2])[2];
            if (($fromRow % ($trackEachRow + 1) == 0) && ($fromRow == $toRow)) { # on power grid
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2]) = 0\n";
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1]) = 0\n";
            }
        }
        print $out "\n";
    }
}
print $out "\n";


### BINARIES
print $out "Binaries\n\n";
print $out "\\ Following variables are binaries, i.e., 0-1 indicators.\n\n";

### Wire binary variables
for my $udeIndex (0 .. $#udEdges) {
    print $out "W($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])\n";
}
for my $vEdgeIndex (0 .. $#virtualEdges) {
    print $out "W($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
}
print $out "\n";

### Metal binary variables
for my $udeIndex (0 .. $#udEdges) {
    print $out "M($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])\n";
}
for my $vEdgeIndex (0 .. $#virtualEdges) {
    print $out "M($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
}

### Extensible Boundary variables [2018-07-06]
# In Extensible Case , Metal binary variables
if ($BoundaryCondition == 1){
    print $out "\\ There are extensible adjacent vertices in L, R, F, B directions.\n\n";
    for my $leftVertex (0 .. $#leftCorners) {
        my $metal = (split /[a-z]/, $leftCorners[$leftVertex])[1];
        if ($metal % 2 == 0) {
            print $out "M(LeftEnd)($leftCorners[$leftVertex])\n";
        }
    }
    for my $rightVertex (0 .. $#rightCorners) {
        my $metal = (split /[a-z]/, $rightCorners[$rightVertex])[1];
        if ($metal % 2 == 0) {
            print $out "M($rightCorners[$rightVertex])(RightEnd)\n";
        }
    }
    for my $frontVertex (0 .. $#frontCorners) {
        my $metal = (split /[a-z]/, $frontCorners[$frontVertex])[1];
        if ($metal % 2 == 1 && $metal>1) {
            print $out "M(FrontEnd)($frontCorners[$frontVertex])\n";
        }
    }
    for my $backVertex (0 .. $#backCorners) {
        my $metal = (split /[a-z]/, $backCorners[$backVertex])[1];
        if ($metal % 2 == 1 && $metal>1) {
            print $out "M($backCorners[$backVertex])(BackEnd)\n";
        }
    }
}

print $out "\n";

### Edge binary variables
for my $netIndex (0 .. $#nets) {
    for my $udeIndex (0 .. $#udEdges) {
        print $out "N$nets[$netIndex][1]\_";
        print $out "E($udEdges[$udeIndex][1])($udEdges[$udeIndex][2])\n";
        print $out "N$nets[$netIndex][1]\_";
        print $out "E($udEdges[$udeIndex][2])($udEdges[$udeIndex][1])\n";
    }
    ### VIRTUAL_EDGE [index] [Origin] [Destination] [Cost=0]
    #@net = ($netName, $netID, $N_pinNets, $source_ofNet, $numSinks, [@sinks_inNet], [@pins_inNet]);
    for my $vEdgeIndex (0 .. $#virtualEdges) {
        if ($virtualEdges[$vEdgeIndex][1] =~ /^pin/) { # source
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
        }
        elsif ($virtualEdges[$vEdgeIndex][2] =~ /^pin/) { # sink
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
        }
        elsif ($virtualEdges[$vEdgeIndex][2] eq $keySON) { # Super Outer Node
            print $out "N$nets[$netIndex][1]\_";
            print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
        }
        
    }
    print $out "\n";
}

### Commodity Flow binary variables
for my $netIndex (0 .. $#nets) {
    for my $commodityIndex (0 .. $nets[$netIndex][4]-1) {
        for my $dEdgeIndex (0 .. $#dEdges) {
            print $out "N$nets[$netIndex][1]\_";
            print $out "C$commodityIndex\_";
            print $out "E($dEdges[$dEdgeIndex][1])($dEdges[$dEdgeIndex][2])\n";
        }
        for my $vEdgeIndex (0 .. $#virtualEdges) {
            if ($virtualEdges[$vEdgeIndex][1] =~ /^pin/) { # source
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
            }
            elsif ($virtualEdges[$vEdgeIndex][2] =~ /^pin/) { # sink
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
            }
            elsif ($virtualEdges[$vEdgeIndex][2] eq $keySON) { # sink
                print $out "N$nets[$netIndex][1]\_";
                print $out "C$commodityIndex\_";
                print $out "E($virtualEdges[$vEdgeIndex][1])($virtualEdges[$vEdgeIndex][2])\n";
            }
        }
        print $out "\n";
    }
}

### Geometric binary variables  
for my $metal (2 .. $numMetalLayer) { # At the top-most metal layer, only vias exist.
    for my $row (0 .. $numTrackH-1) {
        for my $col (0 .. $numTrackV-1) {
            $vName = "m".$metal."r".$row."c".$col;
            if ($metal % 2 == 0) {
                print $out "GL_V($vName)\n";
                print $out "GR_V($vName)\n";
            }
            else {
                print $out "GF_V($vName)\n";
                print $out "GB_V($vName)\n";
            }
        }
    }
}
print $out "\n";
print "have been written.\n";

### END of CPLEX inputfile
print $out "End\n\n\n";

close ($out);

print "a   ILP Formulation File Complete!!\n";
print "a   CPLEX LP FILE: $outfile\n\n";
