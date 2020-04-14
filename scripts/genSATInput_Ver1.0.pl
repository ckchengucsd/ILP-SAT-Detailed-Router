#! /usr/bin/perl

use strict 'vars';
use strict 'refs';
use strict 'subs';

use POSIX;

use Cwd;
### Revision History : Ver 1.0 #####
# 2019-11-26 Initial Release
### Pre-processing ########################################################
my $ARGC        = @ARGV;
my $workdir     = getcwd();
my $infile      = "";
my $outfile     = "";
my $debug       = 0;

my $wireEnable  = 0;  # Wire Segment Enable, 0: Disable, 1: Enable
my $encodeEnable = 6; # Encoding Enable, 0: Disable, 1: Enable (Pair-wise) , 2: Enable (Bimander)
my $BCPEnable = 1;    # BCP Enable, 0: Disable, 1: Enable

if ($ARGC < 1) {
    print "\n*** Error:: Wrong CMD";
    print "\n   [USAGE]: ./PL_FILE [inputfile_ILP]\n\n";
    exit(-1);
}
else {
    $infile     = $ARGV[0];
}

### Encoding Parameters
my $bimanderDivideParam = 2;
my $commandDivideParam = 3;

my $AtLeastVariable = 6;
################################

if (!-e "./$infile") {
    print "\n*** Error:: FILE DOES NOT EXIST..\n";
    print "***         $workdir/$infile\n\n";
    exit(-1);
} else {
    print "\n";
    print "a   Ver. Info. 1.0\n";

    print "a   Generating SAT inputfile (CNF files) based on the following files.\n";
    print "a     Input ILP File:   $workdir/$infile\n";
}

### Output Directory Creation, please see the following reference:
my $seedName = (split /\W+/, $infile)[1];
my $outdir = "$workdir/inputsSAT";
system "mkdir -p $outdir";


### COLLECT PIN INFORMATION, e.g., SOURCES, SINKS, etc.
### HASH of ARRAYS
### PINS [0: s|t|x] [1: netID] [2: commodityID]
my %pins = ();
my @sources = ();
my @sinks = ();
my @outers = ();
my @nets = ();
my %outerAccessVertices = ();
my %innerAccessVertices = ();
my $infileStatus = -1;
my $patternIndex = 0;
my $ilpset = 0;
my @tempArr = ();
my $numNets = 0;
my $numTrackH = 0;
my $numTrackV = 0;
my $numMetalLayer = 4;

my $keySON = "pinSON";

my @outerPinNet = ();

open (my $in, "./$infile");

my %h_sources = ();
my %h_sinks = ();
my %h_nets = ();
while (<$in>) {
    my $line = $_;
    chomp $line;
    if ($line =~ /^\\\s*(\d+).\s/) {
        $infileStatus = $1;
        $patternIndex = 0;
        next;
    }
    if ($infileStatus < 1) {
        if ($line =~ /List of Sources/) {
            push @sources, "pin".$1 while $line =~ /pin(\S+)/g;
            $h_sources{"pin".$1} = 1 while $line =~ /pin(\S+)/g;
        }
        elsif ($line =~ /List of Nets/) {
            push @nets, $1 while $line =~ /net(\S+)/g;
            $h_nets{$1} = 1 while $line =~ /net(\S+)/g;
			if($numNets != (keys %h_nets)){
				print "[ERROR] Net Count Mismatch!! $numNets ".(keys %h_nets)."\n";
				exit(-1);
			}
        }
        elsif ($line =~ /List of Sinks/) {
            push @sinks, "pin".$1 while $line =~ /pin(\S+)/g;
            $h_sinks{"pin".$1} = 1 while $line =~ /pin(\S+)/g;
        }
        elsif ($line =~ /List of Outer Pins/) { ### Currently, we don't use outer pins. because we adopt "pinSON"
            push @outers, "pin".$1 while $line =~ /pin(\S+)/g;
        }
        ############# Net information extraction for each outer pin
        elsif ($line =~ /Outer Pins Information/) {
            push @outerPinNet, [$1, $2]  while $line =~ /net(\S+)=(\S+)/g;
        }
        elsif ($line =~ /Vertical Tracks\s*= (\S+)/) {
            $numTrackV = $1;
        }
        elsif ($line =~ /Horizontal Tracks\s*= (\S+)/) {
            $numTrackH = $1;
        }
        elsif ($line =~ /\# Nets\s*= (\S+)/) {
            $numNets = $1;
        }
    } elsif ($infileStatus < 10) {
        next;
    } elsif ($infileStatus == 10) {
        $ilpset = "ILP".$infileStatus;
        if ($line =~ /\=/) {
            @tempArr = split /[\=\>\<\s]+/, $line;
            if (($tempArr[0] =~ /^N(\S+)_C(\S+)_V\((\S+)\)/) && ($tempArr[1] != 0)) {
                if ($tempArr[1] == 1) {
                    $pins{$3} = ["s", $1, ""];
                }
                elsif ($tempArr[1] == -1) {
                    $pins{$3} = ["t", $1, $2];
                    # PinSON is duplicated key... 
                }
            }
        }
    }
}
close ($in);


### DATABASE CONSTRUCTION
###
### 1. Catch Patterns in the given ILP inputfile.
### DATA STRUCTURE:  HASHES of HASHES of ARRAYS
###                  ilp       patterns  pattern
### PATTERN:  [0: patternIndex] [1: isFormulated?] [2: #terms] [3: signPattern]
###
### 2. Build DATA Structure for matching variable names.

my %ilp = ();
my %patterns = ();
my @pattern = ();
my @signsILP = ();
my $signsPattern = "";
my $numILPterms = 0;
my $pinID = -1;
my $netID = -1;
my $commodityID = -1;
my $edgeOrig = "";
my $edgeDest = "";
my $isSource = 0;
my $isSink = 0;
my $isOuterPinAdj = 0;
my $isInnerPinAdj = 0;
my $isPin = 0;
my $isFeasible = 0;
my $isLeftORFront = 0;
my $isRightORBack = 0;
my $adj = "";

my %varHash = ("NULL");
my $varIndex = 1;
my $numVarArr = 0;
my $numVarHash = 0;
my $numVar = 0;
my $numVarNet = 0;

my %givenSol = ();


### Read Inputfile and Build File System Structure
open (my $in, "./$infile");

$infileStatus = -1;
while (<$in>) {
    my $line = $_;
    chomp $line;
    if ($line =~ /^\\\s*(\d+).\s/) {
        $infileStatus = $1;
        $patternIndex = 0;
        @signsILP = ();
        if ($infileStatus == 1) {
            print "a     - Building Data Structure for Pin Information is done.\n";
        }
        elsif ($infileStatus == 2) {
            print "a     - Building Data Structure for ILP Patterns ";
        }
        elsif ($infileStatus == 9) {
            print "is done. \n";
        }
        next;
    }
    if ($line =~ /\\\s/) {
        next;
    }
    if ($line eq "") {
        next;
    }
    if ($infileStatus < 1) {
        next;
    }
    if ( ($infileStatus < 10) || ($infileStatus > 10)) {
        $ilpset = "ILP0".$infileStatus;
        @tempArr = split /[\=\>\<\s]+/, $line;

        ## infileStatus == 1 , CFC 
        if ($tempArr[0] =~ /^N(\S+)_C(\S+)_V\((\S+)\)/) {
            if ((exists($h_sources{$3})) && ($pins{$3}[1] == $1)) {
                @signsILP = ("s");
            }
            elsif ((exists($h_sinks{$3})) && ($pins{$3}[1] == $1) && ($pins{$3}[2] == $2)){
                @signsILP = ("t");
            }
            else {
                @signsILP = ("x");
            }
        }
        elsif ($tempArr[0] =~ /[EMW]\((\S+)\)\((\S+)\)/) {
            $edgeOrig = $1;
            $edgeDest = $2;
            if ($infileStatus == 2) {
                if (exists($h_sources{$edgeDest})){
                    @signsILP = ("i");
                }
                elsif (exists($h_sinks{$edgeDest})){
                    @signsILP = ("t");
                }
                else {
                    @signsILP = ("x");
                    ####[Encoding Enable mode] Net Variable Generation ###########
                    ##### N0_E(ddd)(ooo) , N0_E(ooo)(ddd) => N0(ooo)
                    ##### Only for neither source nor sink. => For AMON (At-Most-One-Net) Case
                    if ( $encodeEnable != 0 ){
                        for my $i (0 .. $numNets-1) {
                            my $tmpNet = "";
                            $tmpNet = "N".$nets[$i]."(".$edgeDest.")";
                            if (exists($varHash{$tmpNet})) {
                                next;
                            } 
                            else {
                                $varHash{$tmpNet} = $varIndex;
                                $varIndex++;
                                $numVarNet++;
                                if ($debug == 1){
#print "c            $tmpNet := $varHash{$tmpNet}    V is added\n";
                                }
                            }
                        }
                    }
                    ############################################
                }
            }
            elsif ($infileStatus == 3) {
                if (exists($h_sources{$edgeDest})){
                    @signsILP = ("i");
                }
                elsif (exists($h_sinks{$edgeOrig})){
                    @signsILP = ("i");
                }
                else {
                    @signsILP = ("x");
                }
            }
            elsif ($infileStatus == 4) {
                if (exists($h_sources{$edgeOrig})){
                    @signsILP = ("s");
                }
                elsif (exists($h_sinks{$edgeDest})){
                    @signsILP = ("t");
                }
                else {
                    @signsILP = ("x");
                }
            }
            elsif ($infileStatus == 5) {
                if ($line =~ /\>\=/) {
                    next;
                }
                else {
                    @signsILP = ("x");
                }
            }
            elsif ($infileStatus == 9) {
                @signsILP = ("v");
            }
            else {
                @signsILP = ("ERROR1");
            }
        }
        elsif ($tempArr[0] =~ /G(\w)_V/) {
            $adj = $1;
            if ($infileStatus == 6) {
                if ($line =~ /<=/) {
                    next;
                }
                if ($adj eq "L") {
                    @signsILP = ("l");
                }
                elsif ($adj eq "R") {
                    @signsILP = ("r");
                }
                elsif ($adj eq "F") {
                    @signsILP = ("f");
                }
                elsif ($adj eq "B") {
                    @signsILP = ("b");
                }
            }
            elsif ($infileStatus == 7) {
                @signsILP = ("g");
            }
            elsif ($infileStatus == 8) {
                @signsILP = ("g");
            }
            elsif ($infileStatus == 11) {
                @signsILP = ("g");
            }
            elsif ($infileStatus == 12) {
                @signsILP = ("g");
            }
            else {
                @signsILP = ("ERROR2");
            }
        }
        else {
            @signsILP = ("ERROR3");
        }

        for (my $i=2; $i<$#tempArr; $i+=2) {
            if ($tempArr[$i-1] eq "+") {
                push @signsILP, "+";
            }
            elsif ($tempArr[$i-1] eq "-") {
                push @signsILP, "-";
            }
        }
        $signsPattern = join "", @signsILP;
        $numILPterms = scalar @signsILP;

        if (exists $ilp{$ilpset}{$signsPattern}) {
            next;
        }
        else {
            @pattern = ($patternIndex, 0, $numILPterms, $signsPattern);
            $ilp{$ilpset}{$signsPattern} = [@pattern];
            $patternIndex++;
            
            if ( $infileStatus == 11){
                print "@pattern\n";
            }
        }
    } elsif ($infileStatus == 10) {
        if ($line =~ /^\\/) {
            next;
        }
        elsif ($line =~ /^Bounds/) {
            print "a     - Building Data Structure for Given Solutions ";
            next;
        }
        elsif ($line =~ /^Binaries/) {
            print "is done. \n";
            print "a     - Building Data Structure for Variables ";
            next;
        }
        elsif ($line =~ /^End/) {
            print "is done. \n";
            next;
        }
        else {

            # Variable Storing

            @tempArr = split /[\=\-\s]+/, $line;
            if ($line =~ /\=/) {
                $givenSol{$tempArr[0]} = $tempArr[1];
            }
            if ($tempArr[0] =~ /^\S+E\((\S+)\)\((\S+)\)$/) {
                my $eOrig = $1;
                my $eDest = $2;
                if ($tempArr[0] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                    if ($1 < $4 || $2 < $5 || $3 < $6) {
                        if (exists($varHash{$tempArr[0]})){
                            next;
                        }
                        else {
                            $varHash{$tempArr[0]} = $varIndex;
                            $varIndex++;
                        }
                    }
                } 
                elsif (exists($h_sources{$eOrig})){
					if (exists($varHash{$tempArr[0]})){
                        next;
                    }
                    else {
                        $varHash{$tempArr[0]} = $varIndex;
                        $varIndex++;
                    }
                }
                elsif (exists($h_sinks{$eDest})){
					if (exists($varHash{$tempArr[0]})){
                        next;
                    }
                    else {
                        $varHash{$tempArr[0]} = $varIndex;
                        $varIndex++;
                    }
                }
                else {
                    next;
                }
            }
            elsif ($tempArr[0] =~ /^M\((\S+)\)\((\S+)\)$/) {
                if (exists($h_sources{$1})){
                    if ($1 eq $keySON){
                        $outerAccessVertices{$2} = $1;
                    }
                    else {
                        $innerAccessVertices{$2} = $1;
                    }
                }
                elsif (exists($h_sinks{$2})){
                    if ($2 eq $keySON){
                        $outerAccessVertices{$1} = $2;
                    }
                    else {
                        $innerAccessVertices{$1} = $2;
                    }
                }

                if (exists($varHash{$tempArr[0]})){
                    next;
                }
                else {
                    $varHash{$tempArr[0]} = $varIndex;
                    $varIndex++;
                }
            }
            else {
                if (exists($varHash{$tempArr[0]})){
                    next;
                }
                else {
                    #### Wire Segment Skipping 
                    if (($wireEnable == 0) && ($tempArr[0] =~ /^W\(\S+\)\(\S+\)$/)){
                        next;
                    }
                    $varHash{$tempArr[0]} = $varIndex;
                    $varIndex++;
                }
            }
        }
    }
}
close ($in);



my $infileStatus = -1;
my $isLogPrinted = 0;
my @termsILP = ();
my @edgePairs = ();
my @infeasibleEdges = ();
my %h_undirectedEdges = ();
my @undirectedEdges = ();
my @terminalEdges = ();
my @normalEdges = ();
my @binary = ();
my $vertex = "";
my $numClauses = 0;
my $numConstraints = 0; # i.e., #ILP lines

my $numClauses_CFC = 0;
my $numClauses_CFC_T = 0;
my $numClauses_CFC_S = 0;
my $numClauses_CFC_NoSS_Pin = 0;
my $numClauses_CFC_NoSS = 0;

my $numClauses_EUV = 0;
my $numClauses_EUV_SS = 0;
my $numClauses_EUV_NoAdj = 0;
my $numClauses_EUV_OuterAdj = 0;
my $numClauses_EUV_InnerAdj = 0;

my $numClauses_MS = 0;

my $numClauses_GV = 0;

my $outerPinFlag = 0;


######## AMO Function ###### Definition ############
$outfile = "$outdir/$seedName".".cnf.tmp";
print "a   Writing SAT Inputfile in CNF (i.e., AND of ORs) format.\n";

open (my $in, "./$infile");
open (my $out, '>', $outfile);

while (<$in>) {
    my $line = $_;
    chomp($line);
    if ($line =~ /^\\\s*(\d+).\s/) {
        $isLogPrinted = 0;
        $infileStatus = $1;
        next;
    }
    if ($line =~ /\\\s/) {
        next;
    }
    if ($line eq "") {
        next;
    }
    if ($infileStatus < 1) {
        next;
    }
    elsif ($infileStatus == 1) {  
        if ($isLogPrinted == 0 ) {
            print "a     1. Commodity flow conservation for each vertex and every connected edge to the vertex.\n";
            print $out "c 1. Commodity flow conservation for each vertex and every connected edge to the vertex.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP01";
        $isSource = 0;
        $isSink = 0;
        $isPin = 0;
        if ($line =~ /=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            $vertex     = $1 while $tempArr[0] =~ /N\S+_C\S+_V\((\S+)\)/g;
            $commodityID= $1 while $tempArr[0] =~ /N\S+_C(\S+)_V\(\S+\)/g;
            $netID      = $1 while $tempArr[0] =~ /N(\S+)_C\S+_V\(\S+\)/g;

            if (exists($h_sources{$vertex}) && ($pins{$vertex}[1] == $netID)) {
                $isSource = 1;
                $isSink = 0;
                $isPin = 1;
                @signsILP = ("s");                
            }
            elsif (exists($h_sinks{$vertex}) && ($pins{$vertex}[1] == $netID) && ($pins{$vertex}[2] == $commodityID)) {
                $isSource = 0;
                $isSink = 1;
                $isPin = 1;
                @signsILP = ("t");

            }

            elsif (exists($h_sources{$vertex}) && ($pins{$vertex}[1] != $netID)) {
                $isSource = 0;
                $isSink = 0;
                $isPin = 1;
                @signsILP = ("x");
            }
            elsif (exists($h_sinks{$vertex}) && (($pins{$vertex}[1] != $netID) || ($pins{$vertex}[2] != $commodityID))) {
                if ( $vertex eq $keySON ){ ### Routine for SON (There is only one right Sink information )                        
                    $outerPinFlag = 0;
                    for my $outerIndex (0 .. $#outerPinNet){
                        if (( $netID eq $outerPinNet[$outerIndex][0] ) && ( $commodityID eq $outerPinNet[$outerIndex][1])){
                            $outerPinFlag = 1;
                            last;
                        }
                    }
                    if ($outerPinFlag == 1){
                        print "a        Extra Super Outer Node: ", $tempArr[0], "=", $vertex, ",", $commodityID, ",", $netID,"\n";
                        $isSource = 0;
                        $isSink =  1;
                        $isPin = 1;
                        @signsILP = ("t");
                    }
                    else {
                        $isSource = 0;
                        $isSink = 0;
                        $isPin = 1;
                        @signsILP = ("x"); 
                    }
                }
                else {
                    $isSource = 0;
                    $isSink = 0;
                    $isPin = 1;
                    @signsILP = ("x");
                }
            }
            else {
                $isSource = 0;
                $isSink = 0;
                $isPin = 0;
                @signsILP = ("x");
            }
            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Collect Un-Directed Edges Only
            @undirectedEdges = ();
            %h_undirectedEdges = ();
            for my $e (0 .. $#termsILP) {
                $termsILP[$e] =~ m/^\S+E\((\S+)\)\((\S+)\)$/;
                my $eOrig = $1;
                my $eDest = $2;
                if ($termsILP[$e] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                    if ($1 < $4 || $2 < $5 || $3 < $6) {
                        push @undirectedEdges, $termsILP[$e];
						$h_undirectedEdges{$termsILP[$e]} = 1;
                    }
                } 
                elsif (exists($h_sources{$eOrig})){
                    push @undirectedEdges, $termsILP[$e];
					$h_undirectedEdges{$termsILP[$e]} = 1;
                }
                elsif (exists($h_sinks{$eDest})){
                    push @undirectedEdges, $termsILP[$e];
					$h_undirectedEdges{$termsILP[$e]} = 1;
                }
            }

            ### Collect Terminal Edges (to pin or from pin)
            @terminalEdges = ();
            @normalEdges = ();
            for my $e (0 .. $#undirectedEdges) {
                if ($undirectedEdges[$e] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                    push @normalEdges, $undirectedEdges[$e];
                } 
                else {
                    push @terminalEdges, $undirectedEdges[$e];
                }
            }

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}   ";
                    if (exists($h_undirectedEdges{$term})){
                        print $out "V";
                    }
                    print $out "\n";
                }
            }

            ###### Exist CNF representation Analysis First ##############
            ##### No Pin , Neither Source or Sink ###### [2018-11-01]
            if ($isSource == 0 && $isSink == 0 && $isPin == 0) {
                if( $debug == 1){
                    print "a    Neither Source nor Sink case. : $termsILP[0]\n";
                }

                ## Case I : CFC_x , No SSP
                ####### Avoid at-most-one cases...
                for my $i (0 .. $#undirectedEdges) {
                    for my $j (0 .. $#undirectedEdges) {
                        if ($i != $j) {
                            print $out " $varHash{$undirectedEdges[$j]}";
                        }
                        else {
                            print $out " -$varHash{$undirectedEdges[$j]}";
                        }
                    }
                    print $out "    0\n";
                    $numClauses++;
                    $numClauses_CFC++;
                    $numClauses_CFC_NoSS++;
                }

                ##### Currently, There is no cases with more than 2 $#terminalEdges ###
                for my $i (0 .. $#terminalEdges-1) {
                    for my $j ($i+1 .. $#terminalEdges) {
                        print $out " -$varHash{$terminalEdges[$i]} -$varHash{$terminalEdges[$j]}    0\n";
                        $numClauses++;
                        $numClauses_CFC++;
                        $numClauses_CFC_NoSS++;
                    }
                }
				
                if ( $#undirectedEdges >= 5 ){ ### There are five flow directions to the vertex... It's Error
                    print "ERROR - There are more than 5 flow directions to the vertex : $termsILP[0]\n";
                    exit(-1);
                }

                for my $i (0 .. $#undirectedEdges-2){
                    for my $j ($i+1 .. $#undirectedEdges-1) {
                        for my $k ($j+1 .. $#undirectedEdges){
                            if ($debug == 1){
                                print "a    -$varHash{$undirectedEdges[$i]} -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}     0\n";
                            }
                            print $out " -$varHash{$undirectedEdges[$i]} -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}     0\n";
                            $numClauses++;
                            $numClauses_CFC++;
                            $numClauses_CFC_NoSS++;
                        }
                    }
                }

            }
            elsif ($isSource == 1 && $isSink == 0 && $isPin == 1) {
                ### Inside Source : EO Costraint (4~5) -> Just Pairwise Constraint
                for my $i (0 .. $#undirectedEdges) {
                    print $out " $varHash{$undirectedEdges[$i]}";
                }
                print $out "    0\n";
                $numClauses++;
                $numClauses_CFC++;
                $numClauses_CFC_S++;

                for my $i (0 .. $#undirectedEdges-1) {
                    for my $j ($i+1 .. $#undirectedEdges) {
                        print $out " -$varHash{$undirectedEdges[$i]} -$varHash{$undirectedEdges[$j]}    0\n";
                        $numClauses++;
                        $numClauses_CFC++;
                        $numClauses_CFC_S++;
                    }
                }
            }


            ############# EO (Exactly-One) Constraint Case. Inside Sink has at-most the number of track variabile for AMO -> Only consider SON case.
            elsif ($isSource == 0 && $isSink == 1 && $isPin == 1) {
                ### ALO : just 1 clause
                for my $i (0 .. $#undirectedEdges) {
                    print $out " $varHash{$undirectedEdges[$i]}";
                }
                print $out "    0\n";
                $numClauses++;
                $numClauses_CFC++;
                $numClauses_CFC_T++;
 
                ### AMO : currently pair-wise encoding . no need auxiliary variables.
                if (($encodeEnable <= 1) || ($#undirectedEdges <= $AtLeastVariable)  ){ # Pair-wise
                    print "a        $termsILP[0]: Pairwise Encoding\n";
                    for my $i (0 .. $#undirectedEdges-1) {
                        for my $j ($i+1 .. $#undirectedEdges) {
                            print $out " -$varHash{$undirectedEdges[$i]} -$varHash{$undirectedEdges[$j]}    0\n";
                            $numClauses++;
                            $numClauses_CFC++;
                            $numClauses_CFC_T++;
                        }
                    }
                }
                elsif ( ($encodeEnable <= 4) || ($encodeEnable == 7) ) { #bimander encoding
                    print "a        $termsILP[0]: Bimander Encoding\n";
                    my $numGroup = ceil(($#undirectedEdges + 1) / $bimanderDivideParam ); # we can select the number of group depending on the performance.
                    my $numPerGroup = ceil(($#undirectedEdges + 1) / $numGroup); 
                    my $numBitGroup = ceil(log($numGroup)/log(2));

                    ####### Auxiliary Variable Generation and Add to the hash ##########
                    my $auxVarName = ""; 
                    for my $i (0 .. $numBitGroup-1){
                        $auxVarName = "N".$netID."_C".$commodityID."_b".$i."(".$vertex.")";
                        if( exists($varHash{$auxVarName})) {
                            next;
                        }
                        else{ # Add to the var Hash
                            $varHash{$auxVarName} = $varIndex;
                            $varIndex++;
                            $numVarNet++;

                            if ($debug == 1){
                                print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                            }
                        }
                    }
                    ####################################################################
                    my $groupIndex = -1; my $groupIndexPrev = -1; my $lastGroup = 0;
                    for my $i (0 .. $#undirectedEdges){
                        $groupIndex = int($i / $numPerGroup);
                        ############## 1st Step : Execute Group AMO ################
                        if( $groupIndexPrev != $groupIndex ){ 
                            my $startIndex = $i; 
                            my $endIndex = $i+$numPerGroup-1;
                            if ( $endIndex >= $#undirectedEdges ){ # The Last Group
                                $endIndex = $#undirectedEdges;
                                $lastGroup = 1;
                            }
                            for my $j ($startIndex .. $endIndex-1){
                                for my $k ($j+1 .. $endIndex){
                                    print $out " -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}    0\n";
                                    if ( $debug == 1 ){
                                        print "a            -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}    0\n";
                                    }
                                    $numClauses++;
                                    $numClauses_CFC++;
                                    $numClauses_CFC_T++;
                                }
                            } 
                        }
                        $groupIndexPrev = $groupIndex;
                        if ($lastGroup == 1){
                            last;
                        }
                    }

                    my $groupIndex = -1;
                    for my $i (0 .. $#undirectedEdges){
                        ################# 2nd Step : bimander Clauses #########################
                        $groupIndex = int($i / $numPerGroup);
                        my $remainder = -1;

                        for my $j (0 .. $numBitGroup-1){
                            $remainder = int($groupIndex % $bimanderDivideParam);
                            $groupIndex = int($groupIndex / $bimanderDivideParam);
                            $auxVarName = "N".$netID."_C".$commodityID."_b".$j."(".$vertex.")";
                            if( exists($varHash{$auxVarName})) {
                            }
                            else{
                                print "ERROR in var Hash. There is no bimander variable..\n\n";
                                exit (-1);
                            }
                            if ($remainder == 0){
                                print $out " -$varHash{$undirectedEdges[$i]} -$varHash{$auxVarName}    0\n";
                                if ( $debug == 1 ){
                                    print " -$varHash{$undirectedEdges[$i]} -$varHash{$auxVarName}    0\n";
                                }
                            }
                            else{
                                print $out " -$varHash{$undirectedEdges[$i]} $varHash{$auxVarName}    0\n";
                                if ( $debug == 1 ){
                                    print " -$varHash{$undirectedEdges[$i]} $varHash{$auxVarName}    0\n";
                                }
                            }
                            $numClauses++;
                            $numClauses_CFC++;
                            $numClauses_CFC_T++;
                        }
                    }
                }
                elsif ($encodeEnable <= 6){ # Commander 
                    if ( $debug == 1 ){
                        print $out "c   CFC_t - Commander Encoding\n";
                    }
                    print "a        CFC_t - Commander Encoding\n";
                    my $numGroup = ceil(($#undirectedEdges + 1) / $commandDivideParam ); # we can select the number of group depending on the performance.
                    my $numPerGroup = ceil(($#undirectedEdges + 1) / $numGroup);

                    ##### Auxiliary Variable Generation ##########3
                    my $auxVarName = ""; 
                    my $numCommander = 0;
                    for my $i (0 .. $numGroup-1){
                        $auxVarName = "N".$netID."_C".$commodityID."_c".$i."(".$vertex.")";
                        if( exists($varHash{$auxVarName})) {
                            next;
                        }
                        else{ # Add to the var Hash
                            $varHash{$auxVarName} = $varIndex;
                            $varIndex++;
                            $numVarNet++;
                            $numCommander++;

                            if ($debug == 1){
                                print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                            }
                        }
                    }     
                    ######################################
                    my $groupIndex = -1; my $groupIndexPrev = -1;
                    #### 1st Level Commander ALO #####
                    for my $i (0 .. $#undirectedEdges){
                        $groupIndex = int( $i / $numPerGroup);
                        if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                            my $startIndex = $i; 
                            my $endIndex = $i+$numPerGroup-1;
                            if ( $endIndex >= $#undirectedEdges ){ # The Last Group
                                $endIndex = $#undirectedEdges;
                            }

                            if( $groupIndex == 0 ){ 
                                $auxVarName = "N".$netID."_C".$commodityID."_c".$groupIndex."(".$vertex.")";
                                if( exists($varHash{$auxVarName})){
                                    print $out " -$varHash{$auxVarName}";
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                            else { ### Group Index is not initial
                                print $out "    0\n";   ## End for previous clause
                                $numClauses++;
                                $numClauses_CFC++;
                                $numClauses_CFC_T++;
                                
                                $auxVarName = "N".$netID."_C".$commodityID."_c".$groupIndex."(".$vertex.")";
                                if( exists($varHash{$auxVarName})){
                                    print $out " -$varHash{$auxVarName}";
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                        }
                        print $out " $varHash{$undirectedEdges[$i]}";
                        $groupIndexPrev = $groupIndex;

                        if( $i == $#undirectedEdges ){  #last Element
                            print $out "    0\n";
                            $numClauses++;
                            $numClauses_CFC++;
                            $numClauses_CFC_T++;

                            last;
                        }
                    }

                    #### 1st Level Commander AMO #####
                    for my $i (0 .. $#undirectedEdges){
                        $groupIndex = int( $i / $numPerGroup);
                        if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                            my $startIndex = $i; 
                            my $endIndex = $i+$numPerGroup-1;
                            if ( $endIndex >= $#undirectedEdges ){ # The Last Group
                                $endIndex = $#undirectedEdges;
                            }
                            $auxVarName = "N".$netID."_C".$commodityID."_c".$groupIndex."(".$vertex.")";
                            if( exists($varHash{$auxVarName})){
                                for my $j ($startIndex .. $endIndex){
                                    print $out " $varHash{$auxVarName} -$varHash{$undirectedEdges[$j]}  0\n";
                                    $numClauses++;
                                    $numClauses_CFC++;
                                    $numClauses_CFC_T++;
                               }
                                # Other member of group
                                for my $j ($startIndex .. $endIndex-1){
                                    for my $k ($j+1 .. $endIndex){
                                        print $out " -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}    0\n";
                                        $numClauses++;
                                        $numClauses_CFC++;
                                        $numClauses_CFC_T++;
                                    }
                                }
                            }
                            else{
                                print "ERROR - There is no command variable in Hash Table\n";
                                exit(-1);
                            }
                        }
                        $groupIndexPrev = $groupIndex;

                        if( $i == $#undirectedEdges ){  #last Element
                            last;
                        }
                       
                    }
                    ############## End 1st Commander EO #########################
                    ### Higher Level AMO ###
                    my $commanderStart = 0; my $commanderEnd = $numCommander-1; my $extraNumCommander = $numCommander;
                    while ( $extraNumCommander > $AtLeastVariable){
                        $numGroup = ceil($extraNumCommander / $commandDivideParam );
                        $numPerGroup = ceil($extraNumCommander / $numGroup);
                        ######### Auxiliary Variable Generation #############
                        $extraNumCommander = 0; # Re-initializing
                        for my $i (0 .. $numGroup-1){
                            $auxVarName = "N".$netID."_C".$commodityID."_c".$numCommander."(".$vertex.")";
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;
                                $numCommander++;

                                $extraNumCommander++;

                                if ($debug == 1){
                                    print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }
                        ####### EO -> ALO ^ AMO ########
                        $groupIndex = -1; $groupIndexPrev = -1; 
                        for my $i ($commanderStart .. $commanderEnd){
                            $groupIndex = int( ($i - $commanderStart) / $numPerGroup);             
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= $commanderEnd ){ # The Last Group
                                    $endIndex = $commanderEnd;
                                }
                                
                                my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                my $newCommandname = "N".$netID."_C".$commodityID."_c".$newCommandIndex."(".$vertex.")";
                                if ( exists($varHash{$newCommandname}) ){
                                    print $out " -$varHash{$newCommandname}";
                               }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);

                                }
                                for my $j ($startIndex .. $endIndex){ 
                                    $auxVarName = "N".$netID."_C".$commodityID."_c".$j."(".$vertex.")";
                                    if( exists($varHash{$auxVarName})){
                                        print $out " $varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                } 
                                ###################
                                print $out "    0\n";
                                $numClauses++;
                                $numClauses_CFC++;
                                $numClauses_CFC_T++;
                            }
                            $groupIndexPrev = $groupIndex;
                        }
                        ############# higher Level AMO #############
                        $groupIndex = -1; $groupIndexPrev = -1; 
                        for my $i ($commanderStart .. $commanderEnd){
                            $groupIndex = int( ($i - $commanderStart) / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= $commanderEnd ){ # The Last Group
                                    $endIndex = $commanderEnd;
                                }
                                
                                my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                my $newCommandname = "N".$netID."_C".$commodityID."_c".$newCommandIndex."(".$vertex.")";

                                # With new Commander 
                                for my $j ($startIndex .. $endIndex){
                                    $auxVarName = "N".$netID."_C".$commodityID."_c".$j."(".$vertex.")";
                                    print $out " $varHash{$newCommandname} -$varHash{$auxVarName}   0\n";
                                    $numClauses++;
                                    $numClauses_CFC++;
                                    $numClauses_CFC_T++;
                                }
                                # Other members of group
                                for my $j ($startIndex .. $endIndex-1){
                                    $auxVarName = "N".$netID."_C".$commodityID."_c".$j."(".$vertex.")";

                                    if ( exists($varHash{$auxVarName}) ){                                    
                                        for my $k ($j+1 .. $endIndex){
                                            my $auxCommanderName = "N".$netID."_C".$commodityID."_c".$k."(".$vertex.")";

                                            print $out " -$varHash{$auxVarName} -$varHash{$auxCommanderName}    0\n";
                                            $numClauses++;
                                            $numClauses_CFC++;
                                            $numClauses_CFC_T++;
                                        }
                                    }
                                    else{
                                        print "ERROR - there is no commander variable in the hash table\n";
                                        exit(-1);
                                    }
                                }
                            }
                            $groupIndexPrev = $groupIndex;
                        }

                        $commanderStart = $commanderEnd + 1;
                        $commanderEnd = $commanderStart + $extraNumCommander - 1;

                    }
                    
                    # Pair-wise
                    my $commanderNameStart = ""; my $commanderNameEnd = "";
                    for my $i ($commanderStart .. $commanderEnd-1){
                        $commanderNameStart = "N".$netID."_C".$commodityID."_c".$i."(".$vertex.")";
                        if (exists($varHash{$commanderNameStart})){
                            for my $j ($i+1 .. $commanderEnd){
                                $commanderNameEnd = "N".$netID."_C".$commodityID."_c".$j."(".$vertex.")";
                                if (exists($varHash{$commanderNameEnd})){
                                    print $out " -$varHash{$commanderNameStart} -$varHash{$commanderNameEnd}    0\n";
                                    $numClauses++;
                                    $numClauses_CFC++;
                                    $numClauses_CFC_T++;
                                }
                                else{
                                    print "ERROR - There is no commander variable in the Hash Table\n";
                                    exit(-1);
                                }
                            }
                        }
                        else{
                            print "ERROR - There is no commander variable in the Hash Table\n";
                            exit(-1);
                        }
                    }
                }
                else{
                    print "ERROR - Abnormal Encoding Argument\n";
                    exit(-1);
                }
            }
            ######################################################################################################
            elsif ($isSource == 0 && $isSink == 0 && $isPin == 1) {
                for my $i (0 .. $#undirectedEdges) {
                    print $out " -$varHash{$undirectedEdges[$i]}    0\n";
                    $numClauses++;
                    $numClauses_CFC++;
                    $numClauses_CFC_NoSS_Pin++;
                }
            }
            else {
                print "ERROR in your ILP01 sets.\n\n";
                exit (-1);
            }
        }
        
    }
    elsif ($infileStatus == 2) {
        if ($isLogPrinted == 0 ) {
            print "a     2. Exclusiveness use of vertex for each vertex and every connected edge to the vertex.\n";
            print $out "c 2. Exclusiveness use of vertex for each vertex and every connected edge to the vertex.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP02";
        $isSource = 0;
        $isSink = 0;
        $isPin = 0;
        $isOuterPinAdj = 0;
        $isInnerPinAdj = 0;
        if ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /N\S+_E\((\S+)\)\((\S+)\)/) {
                $edgeOrig = $1;
                $edgeDest = $2;
                if (exists($h_sources{$edgeDest})){ 
                    $isSource = 1;
                    $isSink = 0;
                    $isOuterPinAdj = 0;
                    $isInnerPinAdj = 0;
                    @signsILP = ("i");

                    ####### For the net which include pins, Naive(Pair-wise) Exact-one CNF Representation ####
                }
                elsif (exists($h_sinks{$edgeDest})){
                    $isSource = 0;
                    $isSink = 1;
                    $isOuterPinAdj = 0;
                    $isInnerPinAdj = 0;
                    @signsILP = ("t");

                    ####### For the net which include pins, Naive(Pair-wise) Exact-one CNF Representation ####
                }
                else {
                    ### Detect if based on Boundary Vertices
                    if (exists $outerAccessVertices{$edgeDest}) {
                        $isOuterPinAdj = 1;
                        $isInnerPinAdj = 0;
                    }
                    elsif (exists $innerAccessVertices{$edgeDest}) {
                        $isOuterPinAdj = 0;
                        $isInnerPinAdj = 1;
                    }
                    else {
                        $isOuterPinAdj = 0;
                        $isInnerPinAdj = 0;
                    }
                    $isSource = 0;
                    $isSink = 0;
                    @signsILP = ("x");

                    ####### At-Most one net (AMON) CNF Representation ###################################
                }
            }

            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Collect Un-Directed Edges Only
            my %edgesNet = ();
            my $eOrig;
            my $eDest;
            @undirectedEdges = ();
            %h_undirectedEdges = ();
            for my $e (0 .. $#termsILP) {
                $termsILP[$e] =~ m/^N(\S+)_E\((\S+)\)\((\S+)\)$/;
                my $n = $1;
                $eOrig = $2;
                $eDest = $3;
                if ($termsILP[$e] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                    if ($1 < $4 || $2 < $5 || $3 < $6) {
						if( exists($varHash{$termsILP[$e]})){
							push @undirectedEdges, $termsILP[$e];
							$h_undirectedEdges{$termsILP[$e]} = 1;
							push @{$edgesNet{$n}}, $termsILP[$e];
						}
                    }
                    else {
						if( exists($varHash{"N".$n."_E"."(".$eDest.")(".$eOrig.")"})) {
							push @undirectedEdges, "N".$n."_E"."(".$eDest.")(".$eOrig.")";
							$h_undirectedEdges{"N".$n."_E"."(".$eDest.")(".$eOrig.")"} = 1;
							push @{$edgesNet{$n}}, "N".$n."_E"."(".$eDest.")(".$eOrig.")";
						}
                    }
                } 
                elsif (exists($h_sources{$eOrig})){
					if( exists($varHash{$termsILP[$e]})){
						push @undirectedEdges, $termsILP[$e];
						$h_undirectedEdges{$termsILP[$e]} = 1;
						push @{$edgesNet{$n}}, $termsILP[$e];
					}
                }
                elsif (exists($h_sources{$eDest})){ 
					if( exists($varHash{"N".$n."_E"."(".$eDest.")(".$eOrig.")"})) {
						push @undirectedEdges, "N".$n."_E"."(".$eDest.")(".$eOrig.")";
						$h_undirectedEdges{"N".$n."_E"."(".$eDest.")(".$eOrig.")"} = 1;
						push @{$edgesNet{$n}}, "N".$n."_E"."(".$eDest.")(".$eOrig.")";
					}
                }
                elsif (exists($h_sinks{$eDest})){ 
					if( exists($varHash{$termsILP[$e]})){
						push @undirectedEdges, $termsILP[$e];
						$h_undirectedEdges{$termsILP[$e]} = 1;
						push @{$edgesNet{$n}}, $termsILP[$e];
					}
                }
                elsif (exists($h_sinks{$eOrig})){ 
					if( exists($varHash{"N".$n."_E"."(".$eDest.")(".$eOrig.")"})) {
						push @undirectedEdges, "N".$n."_E"."(".$eDest.")(".$eOrig.")";
						$h_undirectedEdges{"N".$n."_E"."(".$eDest.")(".$eOrig.")"} = 1;
						push @{$edgesNet{$n}}, "N".$n."_E"."(".$eDest.")(".$eOrig.")";
					}
                }
            } 

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                for my $i (0 .. $#undirectedEdges) {
                    print $out "c     $termsILP[$i] := $varHash{$termsILP[$i]}   ";
                    if ($termsILP[$i] ne $undirectedEdges[$i]) {
                        print $out "=>   $undirectedEdges[$i] := $varHash{$undirectedEdges[$i]}   ";
                    }
                    print $out "V\n";
                }
            }
            
            
            if (($isInnerPinAdj == 1) && ($isOuterPinAdj == 0)) {
                for my $i (0 .. $numNets-1) {
                    my $tmp = "";
                    if ($innerAccessVertices{$eDest} ~~ @sources) {
                        $tmp = "N".$nets[$i]."_E(".$innerAccessVertices{$eDest}.")(".$eDest.")";
                        if (exists($h_undirectedEdges{$tmp})){
                        } else {
							if( exists($varHash{$tmp})){
								push @undirectedEdges, $tmp;
								push @{$edgesNet{$nets[$i]}}, $tmp;
								if ($debug == 1) {
									print $out "c     $tmp := $varHash{$tmp}    V\n";
								}
							}
                        }
                    }
                    elsif ($innerAccessVertices{$eDest} ~~ @sinks) {
                        $tmp = "N".$nets[$i]."_E(".$eDest.")(".$innerAccessVertices{$eDest}.")";
                        if (exists($h_undirectedEdges{$tmp})){
                        }
                        else {
							if( exists($varHash{$tmp})){
								push @undirectedEdges, $tmp;
								push @{$edgesNet{$nets[$i]}}, $tmp;
								if ($debug == 1) {
									print $out "c     $tmp := $varHash{$tmp}    V\n";
								}
							}
                        }
                    }
                }
            }
            elsif (($isInnerPinAdj == 0) && ($isOuterPinAdj == 1)) {
                for my $i (0 .. $numNets-1) {
                    my $tmp = "N".$nets[$i]."_E(".$eDest.")(".$keySON.")";
                    if( exists($varHash{$tmp}) ){
                        push @undirectedEdges, $tmp;
                        push @{$edgesNet{$nets[$i]}}, $tmp;
                    } 
                    else{
                        next;
                    }
                }
            }


            #### Print EUV Clauses
#           Actually Case I / Case II / Case III has the same code of net variables and AMO for net variable
            #### Case I : No Inner Pin / No Outer Pin -> AMON (At-Most-One Net) ######
            if ($isSource == 0 && $isSink == 0 && $isOuterPinAdj == 0 && $isInnerPinAdj == 0) {
                
                print $out "c EUV-NoAdj ($eDest)\n";

                if ( $encodeEnable == 0){ 
                    foreach my $key1 (keys %edgesNet){
                        for my $i (0 .. $#{$edgesNet{$key1}}) {
                            foreach my $key2 (keys %edgesNet){
                                if ($key1 eq $key2) {
                                    next;
                                }
                                for my $j (0 .. $#{$edgesNet{$key2}}) {
                                    print $out " -$varHash{$edgesNet{$key1}[$i]} -$varHash{$edgesNet{$key2}[$j]}    0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_NoAdj++;

                                }
                            }
                        }
                    }
                }
                else { # Encoding Enable                 
                    #### Checking the net variables (AUX variable) ####
                    for my $i (0 .. $numNets-1) {
                        my $tmpNet = "";
                        $tmpNet = "N".$nets[$i]."(".$eDest.")";
                        if ( exists($varHash{$tmpNet}) == 0 ){
                            print "Net Variable is not in the variable array..!!\n\n";
                            exit (-1);
                        }
                        ##### Feasibility of Net Variale : Logically ORing (The same with Wire segment) 
                        ### Net Variables Pattern (the same with wire segment) ####
                        print $out " -$varHash{$tmpNet}";

                        foreach my $key1 (keys %edgesNet){
                            if ($nets[$i] eq $key1){
                                for my $j (0 .. $#{$edgesNet{$key1}}){ 
                                    print $out " $varHash{$edgesNet{$key1}[$j]}";
                                }
                            }
                        }
                        print $out "    0\n";
                        $numClauses++;
                        $numClauses_EUV++;
                        $numClauses_EUV_NoAdj++;
                        foreach my $key1 (keys %edgesNet){
                            if ($nets[$i] eq $key1){
                                for my $j (0 .. $#{$edgesNet{$key1}}){ 
                                    print $out " $varHash{$tmpNet} -$varHash{$edgesNet{$key1}[$j]}  0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_NoAdj++;
                                }
                            }
                        }
                    }
                    ######################## AMO for Net Variable : 1/2. Pair-wise, 3. Bimander ###################
                    if ( $debug == 1){
                        print $out "c   AMO for net variables\n";
                    }

                    if (($encodeEnable <= 2) || ($numNets <= $AtLeastVariable)){  # 1. Pairwise ( The same with MAR )
                        if ( $debug == 1){
                            print $out " Pairwise (1)\n";
                        }
                        for my $i (0 .. $numNets-2) {
                            my $tmpNet_i = "";
                            $tmpNet_i = "N".$nets[$i]."(".$eDest.")";
                            for my $j ($i+1 .. $numNets-1) {
                                my $tmpNet_j = "";
                                $tmpNet_j = "N".$nets[$j]."(".$eDest.")";
                                print $out " -$varHash{$tmpNet_i} -$varHash{$tmpNet_j}    0\n";
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_NoAdj++;
                            }
                        }
                    }
                    elsif ( ($encodeEnable <= 5) || ($encodeEnable == 7)){
                        if ( $debug == 1 ){
                            print $out " Bimander (2)\n";
                        }
                        my $numGroup = ceil(($numNets) / $bimanderDivideParam ); # we can select the number of group depending on the performance.
                        my $numPerGroup = ceil(($numNets) / $numGroup); 
                        my $numBitGroup = ceil(log($numGroup)/log(2));

                        my $auxVarName = ""; 
                        for my $i (0 .. $numBitGroup-1){
                            $auxVarName = "N_b".$i."(".$eDest.")";
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;

                                if ($debug == 1){
	                               print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }
                        ####################################################################
                        my $groupIndex = -1; my $groupIndexPrev = -1; my $lastGroup = 0;
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int($i / $numPerGroup);
                            ############## 1st Step : Execute Group AMO ################
                            if( $groupIndexPrev != $groupIndex ){
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = $numNets-1;
                                    $lastGroup = 1;
                                }
                                for my $j ($startIndex .. $endIndex-1){
                                    my $auxVarName_j = "N".$nets[$j]."(".$eDest.")";
                                    for my $k ($j+1 .. $endIndex){
                                        my $auxVarName_k = "N".$nets[$k]."(".$eDest.")";
                                        print $out " -$varHash{$auxVarName_j} -$varHash{$auxVarName_k}    0\n";
                                        if ( $debug == 1 ){
                                             print " -$varHash{$auxVarName_j} -$varHash{$auxVarName_k}    0\n";
                                        }
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_NoAdj++;
                                    }
                                }
                               
                            }
                            $groupIndexPrev = $groupIndex;
                            if ($lastGroup == 1){
                               last;
                            }
                        }
                        my $groupIndex = -1;
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int($i / $numPerGroup);
                            my $remainder = -1;

                            my $auxVarName = "N".$nets[$i]."(".$eDest.")";
                            for my $j (0 .. $numBitGroup-1){
                                $remainder = int($groupIndex % 2);
                                $groupIndex = int($groupIndex / 2);
                                my $auxBitName = "N_b".$j."(".$eDest.")";

                                if( exists($varHash{$auxBitName })) {
                                }
                                else{
                                    print "ERROR in var Hash. There is no bimander variable..\n\n";
                                    exit (-1);
                                }
                                if ($remainder == 0){
                                    print $out " -$varHash{$auxVarName} -$varHash{$auxBitName}    0\n";
                                    if ( $debug == 1 ){
                                        print " -$varHash{$auxVarName} -$varHash{$auxBitName}    0\n";
                                    }
                                }
                                else{
                                    print $out " -$varHash{$auxVarName} $varHash{$auxBitName}    0\n";
                                    if ( $debug == 1 ){
                                        print " -$varHash{$auxVarName} $varHash{$auxBitName}    0\n";
                                    }
                                }
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_NoAdj++;
                            }
                        } 
                    }
                    elsif ( $encodeEnable == 6 ){ # Commander Mode
                        if ( $debug == 1){
                            print "a    Commander Encoding (No Adj)\n";
                        }
                        my $numGroup = ceil( ($numNets) / $commandDivideParam ); # we can select the number of group depending on the performance.
                        my $numPerGroup = ceil(($numNets) / $numGroup);

                        ##### Auxiliary Variable Generation ##########3
                        my $auxVarName = ""; 
                        my $numCommander = 0;
                        for my $i (0 .. $numGroup-1){
                            $auxVarName = "N_c".$i."(".$eDest.")";
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;
                                $numCommander++;

                                if ($debug == 1){
                                    print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }     
                        my $groupIndex = -1; my $groupIndexPrev = -1;
                        #### 1st Level Commander ALO #####
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int( $i / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = ($numNets-1);
                                }

                                if( $groupIndex == 0 ){ 
                                    $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                    if( exists($varHash{$auxVarName})){
                                        print $out " -$varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                }
                                else { ### Group Index is not initial
                                    print $out "    0\n";   ## End for previous clause
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_NoAdj++;
                                    
                                    $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                    if( exists($varHash{$auxVarName})){
                                        print $out " -$varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                }
                            }
                            my $auxNetVariable = "N".$nets[$i]."(".$eDest.")";
                            if ( exists ($varHash{$auxNetVariable} )){
                                print $out " $varHash{$auxNetVariable}";
                                $groupIndexPrev = $groupIndex;
                            }
                            else{
                                print "ERROR : There is no Net Varaible in the Hash Table\n";
                                exit(-1);
                            }
                            
                            if( $i == ($numNets-1) ){  #last Element
                                print $out "    0\n";
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_NoAdj++;
                                
                                last;
                            }
                        }
                        #### 1st Level Commander AMO #####
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int( $i / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = $numNets-1;
                                }
                                $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                if( exists($varHash{$auxVarName})){
                                    for my $j ($startIndex .. $endIndex){
                                        my $auxNetVariable = "N".$nets[$j]."(".$eDest.")";
                                        print $out " $varHash{$auxVarName} -$varHash{$auxNetVariable}  0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_NoAdj++;
                                    }
                                    # Other member of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        my $auxNetVariable_j = "N".$nets[$j]."(".$eDest.")";
                                        for my $k ($j+1 .. $endIndex){
                                            my $auxNetVariable_k = "N".$nets[$k]."(".$eDest.")";
                                            print $out " -$varHash{$auxNetVariable_j} -$varHash{$auxNetVariable_k}    0\n";
                                            $numClauses++;
                                            $numClauses_EUV++;
                                            $numClauses_EUV_NoAdj++;
                                        }
                                    }
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                            $groupIndexPrev = $groupIndex;
                            if( $i == $numNets-1 ){  #last Element
                                last;
                            }
                        }
                        ############## End 1st Commander EO #########################
                        
                        ### Commander Iterative Generation ###
                        ### Higher Level AMO ###
                        my $commanderStart = 0; my $commanderEnd = $numCommander-1; my $extraNumCommander = $numCommander;
                        while ( $extraNumCommander > $AtLeastVariable){
                            $numGroup = ceil($extraNumCommander / $commandDivideParam );
                            $numPerGroup = ceil($extraNumCommander / $numGroup);
                            
                            ######### Auxiliary Variable Generation #############
                            $extraNumCommander = 0; # Re-initializing
                            for my $i (0 .. $numGroup-1){
                                $auxVarName = "N_c".$numCommander."(".$eDest.")";
                                if( exists($varHash{$auxVarName})) {
                                    next;
                                }
                                else{ # Add to the var Hash
                                    $varHash{$auxVarName} = $varIndex;
                                    $varIndex++;
                                    $numVarNet++;
                                    $numCommander++;

                                    $extraNumCommander++;

                                    if ($debug == 1){
                                        print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                    }
                                }
                            }
                            ####### EO -> ALO ^ AMO ########
                            $groupIndex = -1; $groupIndexPrev = -1; 
                            for my $i ($commanderStart .. $commanderEnd){
                                $groupIndex = int( ($i - $commanderStart) / $numPerGroup);             
                                if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                    my $startIndex = $i; 
                                    my $endIndex = $i+$numPerGroup-1;
                                    if ( $endIndex >= $commanderEnd ){ # The Last Group
                                        $endIndex = $commanderEnd;
                                    }
                                    
                                    my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                    my $newCommandname = "N_c".$newCommandIndex."(".$eDest.")";
                                    if ( exists($varHash{$newCommandname}) ){
                                        print $out " -$varHash{$newCommandname}";
                                   }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);

                                    }
                                    for my $j ($startIndex .. $endIndex){ 
                                        $auxVarName = "N_c".$j."(".$eDest.")";
                                        if( exists($varHash{$auxVarName})){
                                            print $out " $varHash{$auxVarName}";
                                        }
                                        else{
                                            print "ERROR - There is no command variable in Hash Table\n";
                                            exit(-1);
                                        }
                                    } 
                                    ###################
                                    print $out "    0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_NoAdj++;

                                }
                                $groupIndexPrev = $groupIndex;
                            }
                            ############# higher Level AMO #############
                            $groupIndex = -1; $groupIndexPrev = -1; 
                            for my $i ($commanderStart .. $commanderEnd){
                                $groupIndex = int( ($i - $commanderStart) / $numPerGroup);
                                if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                    my $startIndex = $i; 
                                    my $endIndex = $i+$numPerGroup-1;
                                    if ( $endIndex >= $commanderEnd ){ # The Last Group
                                        $endIndex = $commanderEnd;
                                    }
                                    
                                    my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                    my $newCommandname = "N_c".$newCommandIndex."(".$eDest.")";

                                    # With new Commander 
                                    for my $j ($startIndex .. $endIndex){
                                        $auxVarName = "N_c".$j."(".$eDest.")";
                                        print $out " $varHash{$newCommandname} -$varHash{$auxVarName}   0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_NoAdj++;
                                    }
                                    # Other members of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        $auxVarName = "N_c".$j."(".$eDest.")";

                                        if ( exists($varHash{$auxVarName}) ){                                    
                                            for my $k ($j+1 .. $endIndex){
                                                my $auxCommanderName = "N_c".$k."(".$eDest.")";

                                                print $out " -$varHash{$auxVarName} -$varHash{$auxCommanderName}    0\n";
                                                $numClauses++;
                                                $numClauses_EUV++;
                                                $numClauses_EUV_NoAdj++;
                                            }
                                        }
                                        else{
                                            print "ERROR - there is no commander variable in the hash table\n";
                                            exit(-1);
                                        }
                                    }
                                }
                                $groupIndexPrev = $groupIndex;
                            }

                            $commanderStart = $commanderEnd + 1;
                            $commanderEnd = $commanderStart + $extraNumCommander - 1;
                        }

                        # Pair-wise
                        my $commanderNameStart = ""; my $commanderNameEnd = "";
                        for my $i ($commanderStart .. $commanderEnd-1){
                            $commanderNameStart = "N_c".$i."(".$eDest.")";
                            if (exists($varHash{$commanderNameStart})){
                                for my $j ($i+1 .. $commanderEnd){
                                    $commanderNameEnd = "N_c".$j."(".$eDest.")";
                                    if (exists($varHash{$commanderNameEnd})){
                                        print $out " -$varHash{$commanderNameStart} -$varHash{$commanderNameEnd}    0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_NoAdj++;
                                    }
                                    else{
                                        print "ERROR - There is no commander variable in the Hash Table\n";
                                        exit(-1);
                                    }
                                }
                            }
                            else{
                                print "ERROR - There is no commander variable in the Hash Table\n";
                                exit(-1);
                            }
                        }
                    }
                    else{
                        print "ERROR in your encoding enable mode when EUV process.($encodeEnable) \n\n";
                        exit (-1);
                    }
                    ###############################################
                }
            }
            elsif ($isSource == 0 && $isSink == 0 && $isOuterPinAdj == 0 && $isInnerPinAdj == 1) {

                print $out "c EUV-InnerAdj ($eDest)\n";


                if ($encodeEnable == 0) {
                    foreach my $key1 (keys %edgesNet){
                        for my $i (0 .. $#{$edgesNet{$key1}}) {
                            foreach my $key2 (keys %edgesNet){
                                if ($key1 eq $key2) {
                                    next;
                                }
                                for my $j (0 .. $#{$edgesNet{$key2}}) {
                                    print $out " -$varHash{$edgesNet{$key1}[$i]} -$varHash{$edgesNet{$key2}[$j]}    0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_InnerAdj++;

                                }
                            }
                        }
                    }
                }
                else{

                    ### Net Variable Update ###
                    for my $i (0 .. $numNets-1) {
                        my $tmpNet = "";
                        $tmpNet = "N".$nets[$i]."(".$eDest.")";
                        if ( exists($varHash{$tmpNet}) == 0 ){
                            print "Net Variable is not in the variable array..!!\n\n";
                            exit (-1);
                        }
                        ##### Feasibility of Net Variale : Logically ORing (The same with Wire segment) 
                        ### Net Variables Pattern (the same with wire segment) ####
                        print $out " -$varHash{$tmpNet}";
                        foreach my $key1 (keys %edgesNet){
							if($eDest eq "m1r26c38"){
								print "AA $nets[$i] $key1 $edgesNet{$key1}\n";
							}
                            if ($nets[$i] eq $key1){
                                for my $j (0 .. $#{$edgesNet{$key1}}){ 
                                    print $out " $varHash{$edgesNet{$key1}[$j]}";
                                }
                            }
                        }
                        print $out "    0\n";
                        $numClauses++;
                        $numClauses_EUV++;
                        $numClauses_EUV_InnerAdj++;

                        foreach my $key1 (keys %edgesNet){
                            if ($nets[$i] eq $key1){
                                for my $j (0 .. $#{$edgesNet{$key1}}){ 
                                    print $out " $varHash{$tmpNet} -$varHash{$edgesNet{$key1}[$j]}  0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_InnerAdj++;
                                }
                            }
                        }
                    }
                    ######################## AMO for Net Variable : 1. Pair-wise, 2. Bimander ###################
                    if ($debug == 1){
                        print $out "c   AMO for net variables\n";
                    }
                    if (($encodeEnable <= 2) || ($numNets <= $AtLeastVariable)){  # 1. Pairwise ( The same with MAR )
                        if ($debug == 1){
                            print $out " Pairwise (1)\n";
                        }
                        for my $i (0 .. $numNets-2) {
                            my $tmpNet_i = "";
                            $tmpNet_i = "N".$nets[$i]."(".$eDest.")";
                            for my $j ($i+1 .. $numNets-1) {
                                my $tmpNet_j = "";
                                $tmpNet_j = "N".$nets[$j]."(".$eDest.")";
                                print $out " -$varHash{$tmpNet_i} -$varHash{$tmpNet_j}    0\n";
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_InnerAdj++;
                            }
                        }
                    }
                    elsif ( ($encodeEnable <= 5) || ($encodeEnable == 7)){
                        if ( $debug == 1){
                            print $out " Bimander (2) - InnerAdj Case\n";
                        }
                        my $numGroup = ceil(($numNets) / $bimanderDivideParam ); # we can select the number of group depending on the performance.
                        my $numPerGroup = ceil(($numNets) / $numGroup); 
                        my $numBitGroup = ceil(log($numGroup)/log(2));
                        ####### Auxiliary Variable Generation and Add to the hash ##########
                        my $auxVarName = ""; 
                        for my $i (0 .. $numBitGroup-1){
                            $auxVarName = "N_b".$i."(".$eDest.")";
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;

                                if ($debug == 1){
                                    print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }
                        ####################################################################
                        my $groupIndex = -1; my $groupIndexPrev = -1; my $lastGroup = 0;
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int($i / $numPerGroup);
                            ############## 1st Step : Execute Group AMO ################
                            if( $groupIndexPrev != $groupIndex ){
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = $numNets-1;
                                    $lastGroup = 1;
                                }
                                for my $j ($startIndex .. $endIndex-1){
                                    my $auxVarName_j = "N".$nets[$j]."(".$eDest.")";
                                    for my $k ($j+1 .. $endIndex){
                                        my $auxVarName_k = "N".$nets[$k]."(".$eDest.")";
                                        print $out " -$varHash{$auxVarName_j} -$varHash{$auxVarName_k}    0\n";
                                        if ( $debug == 1 ){
                                             print " -$varHash{$auxVarName_j} -$varHash{$auxVarName_k}    0\n";
                                        }
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_InnerAdj++;
                                    }
                                }  
                            }
                            $groupIndexPrev = $groupIndex;
                            if ($lastGroup == 1){
                                last;
                            }
                        }
                        my $groupIndex = -1;
                        for my $i (0 .. $numNets-1){
                            ################# 2nd Step : bimander Clauses #########################
                            $groupIndex = int($i / $numPerGroup);
                            my $remainder = -1;

                            my $auxVarName = "N".$nets[$i]."(".$eDest.")";

                            for my $j (0 .. $numBitGroup-1){
                                $remainder = int($groupIndex % 2);
                                $groupIndex = int($groupIndex / 2);
                                my $auxBitName = "N_b".$j."(".$eDest.")";
                                if( exists($varHash{$auxBitName })) {
                                    print " $auxBitName  := $varHash{$auxBitName }\n";
                                }
                                else{
                                    print "ERROR in var Hash. There is no bimander variable..\n\n";
                                    exit (-1);
                                }
                                if ($remainder == 0){
                                    print $out " -$varHash{$auxVarName} -$varHash{$auxBitName}    0\n";
                                    if ( $debug == 1 ){
                                        print " -$varHash{$auxVarName} -$varHash{$auxBitName}    0\n";
                                    }
                                }
                                else{
                                    print $out " -$varHash{$auxVarName} $varHash{$auxBitName}    0\n";
                                    if ( $debug == 1 ){
                                        print " -$varHash{$auxVarName} $varHash{$auxBitName}    0\n";
                                    }
                                }
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_InnerAdj++;
                            }
                        } 
                    }
                    elsif ( $encodeEnable == 6 ){
                        if ($debug == 1){
                            print "a    Commander Encoding (InnerAdj)\n";
                        }
                        my $numGroup = ceil( ($numNets) / $commandDivideParam ); # we can select the number of group depending on the performance.
                        my $numPerGroup = ceil(($numNets) / $numGroup);

                        ##### Auxiliary Variable Generation ##########3
                        my $auxVarName = ""; 
                        my $numCommander = 0;
                        for my $i (0 .. $numGroup-1){
                            $auxVarName = "N_c".$i."(".$eDest.")";
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;
                                $numCommander++;

                                if ($debug == 1){
                                    print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }     
                        my $groupIndex = -1; my $groupIndexPrev = -1;
                        #### 1st Level Commander ALO #####
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int( $i / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = ($numNets-1);
                                }

                                if( $groupIndex == 0 ){ 
                                    $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                    if( exists($varHash{$auxVarName})){
                                        print $out " -$varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                }
                                else { ### Group Index is not initial
                                    print $out "    0\n";   ## End for previous clause
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_InnerAdj++;
                                    
                                    $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                    if( exists($varHash{$auxVarName})){
                                        print $out " -$varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                }
                            }
                            my $auxNetVariable = "N".$nets[$i]."(".$eDest.")";
                            if ( exists ($varHash{$auxNetVariable} )){
                                print $out " $varHash{$auxNetVariable}";
                                $groupIndexPrev = $groupIndex;
                            }
                            else{
                                print "ERROR : There is no Net Varaible in the Hash Table\n";
                                exit(-1);
                            }
                            
                            if( $i == ($numNets-1) ){  #last Element
                                print $out "    0\n";
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_InnerAdj++;
                                
                                last;
                            }
                        }
                        #### 1st Level Commander AMO #####
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int( $i / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = $numNets-1;
                                }
                                $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                if( exists($varHash{$auxVarName})){
                                    for my $j ($startIndex .. $endIndex){
                                        my $auxNetVariable = "N".$nets[$j]."(".$eDest.")";
                                        print $out " $varHash{$auxVarName} -$varHash{$auxNetVariable}  0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_InnerAdj++;
                                   }
                                    # Other member of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        my $auxNetVariable_j = "N".$nets[$j]."(".$eDest.")";
                                        for my $k ($j+1 .. $endIndex){
                                            my $auxNetVariable_k = "N".$nets[$k]."(".$eDest.")";
                                            print $out " -$varHash{$auxNetVariable_j} -$varHash{$auxNetVariable_k}    0\n";
                                            $numClauses++;
                                            $numClauses_EUV++;
                                            $numClauses_EUV_InnerAdj++;
                                        }
                                    }
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                            $groupIndexPrev = $groupIndex;
                            if( $i == $numNets-1 ){  #last Element
                                last;
                            }
                        }
                        ############## End 1st Commander EO #########################
                        
                        ### Commander Iterative Generation ###
                        ### Higher Level AMO ###
                        my $commanderStart = 0; my $commanderEnd = $numCommander-1; my $extraNumCommander = $numCommander;
                        while ( $extraNumCommander > $AtLeastVariable){
                            $numGroup = ceil($extraNumCommander / $commandDivideParam );
                            $numPerGroup = ceil($extraNumCommander / $numGroup);
                            ######### Auxiliary Variable Generation #############
                            $extraNumCommander = 0; # Re-initializing
                            for my $i (0 .. $numGroup-1){
                                $auxVarName = "N_c".$numCommander."(".$eDest.")";
                                if( exists($varHash{$auxVarName})) {
                                    next;
                                }
                                else{ # Add to the var Hash
                                    $varHash{$auxVarName} = $varIndex;
                                    $varIndex++;
                                    $numVarNet++;
                                    $numCommander++;

                                    $extraNumCommander++;

                                    if ($debug == 1){
                                       print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                    }
                                }
                            }
                            ####### EO -> ALO ^ AMO ########
                            $groupIndex = -1; $groupIndexPrev = -1; 
                            for my $i ($commanderStart .. $commanderEnd){
                                $groupIndex = int( ($i - $commanderStart) / $numPerGroup);             
                                if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                    my $startIndex = $i; 
                                    my $endIndex = $i+$numPerGroup-1;
                                    if ( $endIndex >= $commanderEnd ){ # The Last Group
                                        $endIndex = $commanderEnd;
                                    }
                                    
                                    my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                    my $newCommandname = "N_c".$newCommandIndex."(".$eDest.")";
                                    if ( exists($varHash{$newCommandname}) ){
                                        print $out " -$varHash{$newCommandname}";
                                   }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);

                                    }
                                    for my $j ($startIndex .. $endIndex){ 
                                        $auxVarName = "N_c".$j."(".$eDest.")";
                                        if( exists($varHash{$auxVarName})){
                                            print $out " $varHash{$auxVarName}";
                                        }
                                        else{
                                            print "ERROR - There is no command variable in Hash Table\n";
                                            exit(-1);
                                        }
                                    } 
                                    ###################
                                    print $out "    0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_InnerAdj++;

                                }
                                $groupIndexPrev = $groupIndex;
                            }
                            ############# higher Level AMO #############
                            $groupIndex = -1; $groupIndexPrev = -1; 
                            for my $i ($commanderStart .. $commanderEnd){
                                $groupIndex = int( ($i - $commanderStart) / $numPerGroup);
                                if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                    my $startIndex = $i; 
                                    my $endIndex = $i+$numPerGroup-1;
                                    if ( $endIndex >= $commanderEnd ){ # The Last Group
                                        $endIndex = $commanderEnd;
                                    }
                                    
                                    my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                    my $newCommandname = "N_c".$newCommandIndex."(".$eDest.")";

                                    # With new Commander 
                                    for my $j ($startIndex .. $endIndex){
                                        $auxVarName = "N_c".$j."(".$eDest.")";
                                        print $out " $varHash{$newCommandname} -$varHash{$auxVarName}   0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_InnerAdj++;
                                    }
                                    # Other members of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        $auxVarName = "N_c".$j."(".$eDest.")";

                                        if ( exists($varHash{$auxVarName}) ){                                    
                                            for my $k ($j+1 .. $endIndex){
                                                my $auxCommanderName = "N_c".$k."(".$eDest.")";

                                                print $out " -$varHash{$auxVarName} -$varHash{$auxCommanderName}    0\n";
                                                $numClauses++;
                                                $numClauses_EUV++;
                                                $numClauses_EUV_InnerAdj++;
                                            }
                                        }
                                        else{
                                            print "ERROR - there is no commander variable in the hash table\n";
                                            exit(-1);
                                        }
                                    }
                                }
                                $groupIndexPrev = $groupIndex;
                            }

                            $commanderStart = $commanderEnd + 1;
                            $commanderEnd = $commanderStart + $extraNumCommander - 1;

                        }
                        # Pair-wise
                        my $commanderNameStart = ""; my $commanderNameEnd = "";
                        for my $i ($commanderStart .. $commanderEnd-1){
                            $commanderNameStart = "N_c".$i."(".$eDest.")";
                            if (exists($varHash{$commanderNameStart})){
                                for my $j ($i+1 .. $commanderEnd){
                                    $commanderNameEnd = "N_c".$j."(".$eDest.")";
                                    if (exists($varHash{$commanderNameEnd})){
                                        print $out " -$varHash{$commanderNameStart} -$varHash{$commanderNameEnd}    0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_InnerAdj++;
                                    }
                                    else{
                                        print "ERROR - There is no commander variable in the Hash Table\n";
                                        exit(-1);
                                    }
                                }
                            }
                            else{
                                print "ERROR - There is no commander variable in the Hash Table\n";
                                exit(-1);
                            }
                        }

                    }
                    else{
                        print "ERROR in your encoding enable mode when EUV process.($encodeEnable) \n\n";

                        exit (-1);
                    }
                    ###############################################
                }
                #################################
            }
            elsif ($isSource == 0 && $isSink == 0 && $isOuterPinAdj == 1 && $isInnerPinAdj == 0) {

                print $out "c EUV-OuterAdj ($eDest)\n";


                if ($encodeEnable == 0) {
                    foreach my $key1 (keys %edgesNet){
                        for my $i (0 .. $#{$edgesNet{$key1}}) {
                            foreach my $key2 (keys %edgesNet){
                                if ($key1 eq $key2) {
                                    next;
                                }
                                for my $j (0 .. $#{$edgesNet{$key2}}) {
                                    print $out " -$varHash{$edgesNet{$key1}[$i]} -$varHash{$edgesNet{$key2}[$j]}    0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_OuterAdj++;

                                }
                            }
                        }
                    }
                }
                else{
                    for my $i (0 .. $numNets-1) {
                        my $tmpNet = "";
                        $tmpNet = "N".$nets[$i]."(".$eDest.")";
                        if ( exists($varHash{$tmpNet}) == 0 ){
                            print "Net Variable is not in the variable array..!!\n\n";
                            exit (-1);
                        }

                        ##### Feasibility of Net Variale : Logically ORing (The same with Wire segment) 
                        ### Net Variables Pattern (the same with wire segment) ####
                        print $out " -$varHash{$tmpNet}";
                        foreach my $key1 (keys %edgesNet){
                            if ($nets[$i] eq $key1){
                                for my $j (0 .. $#{$edgesNet{$key1}}){ 
                                    print $out " $varHash{$edgesNet{$key1}[$j]}";
                                }
                            }
                        }
                        print $out "    0\n";
                        $numClauses++;
                        $numClauses_EUV++;
                        $numClauses_EUV_OuterAdj++;

                        foreach my $key1 (keys %edgesNet){
                            if ($nets[$i] eq $key1){
                                for my $j (0 .. $#{$edgesNet{$key1}}){ 
                                    print $out " $varHash{$tmpNet} -$varHash{$edgesNet{$key1}[$j]}  0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_OuterAdj++;
                                }
                            }
                        }
                    }
                    ######################## AMO for Net Variable : 1. Pair-wise, 2. Bimander ###################
                    if ($debug == 1){
                        print $out "c   AMO for net variables\n";
                    }
                    if (($encodeEnable <= 2) || ($numNets <= $AtLeastVariable)){  # 1. Pairwise ( The same with MAR )
                        if ($debug == 1){    
                            print $out " Pairwise (1)\n";
                        }
                        for my $i (0 .. $numNets-2) {
                            my $tmpNet_i = "";
                            $tmpNet_i = "N".$nets[$i]."(".$eDest.")";
                            for my $j ($i+1 .. $numNets-1) {
                                my $tmpNet_j = "";
                                $tmpNet_j = "N".$nets[$j]."(".$eDest.")";
                                print $out " -$varHash{$tmpNet_i} -$varHash{$tmpNet_j}    0\n";
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_OuterAdj++;
                            }
                        }
                    }
                    elsif (($encodeEnable <= 5) || ($encodeEnable == 7)){
                        if ($debug == 1){
                            print $out " Bimander (2)\n";
                        }
                        my $numGroup = ceil(($numNets) / $bimanderDivideParam ); # we can select the number of group depending on the performance.
                        my $numPerGroup = ceil(($numNets) / $numGroup); 
                        my $numBitGroup = ceil(log($numGroup)/log(2));

                        ####### Auxiliary Variable Generation and Add to the hash ##########
                        my $auxVarName = ""; 
                        for my $i (0 .. $numBitGroup-1){
                            $auxVarName = "N_b".$i."(".$eDest.")";
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;

                                if ($debug == 1){
                                    print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }
                        ####################################################################
                        my $groupIndex = -1; my $groupIndexPrev = -1; my $lastGroup = 0;
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int($i / $numPerGroup);
                            ############## 1st Step : Execute Group AMO ################
                            if( $groupIndexPrev != $groupIndex ){
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = $numNets-1;
                                    $lastGroup = 1;
                                }
                                for my $j ($startIndex .. $endIndex-1){
                                    my $auxVarName_j = "N".$nets[$j]."(".$eDest.")";
                                    for my $k ($j+1 .. $endIndex){
                                        my $auxVarName_k = "N".$nets[$k]."(".$eDest.")";
                                        print $out " -$varHash{$auxVarName_j} -$varHash{$auxVarName_k}    0\n";
                                        if ( $debug == 1 ){
                                             print " -$varHash{$auxVarName_j} -$varHash{$auxVarName_k}    0\n";
                                        }
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_OuterAdj++;
                                    }
                                }  
                            }
                            $groupIndexPrev = $groupIndex;
                            if ($lastGroup == 1){
                                last;
                            }
                        }
                        my $groupIndex = -1;
                        for my $i (0 .. $numNets-1){
                            ################# 2nd Step : bimander Clauses #########################
                            $groupIndex = int($i / $numPerGroup);
                            my $remainder = -1;

                            my $auxVarName = "N".$nets[$i]."(".$eDest.")";

                            for my $j (0 .. $numBitGroup-1){
                                $remainder = int($groupIndex % 2);
                                $groupIndex = int($groupIndex / 2);
                                my $auxBitName = "N_b".$j."(".$eDest.")";
                                if( exists($varHash{$auxBitName })) {
                                }
                                else{
                                    print "ERROR in var Hash. There is no bimander variable..\n\n";
                                    exit (-1);
                                }
                                if ($remainder == 0){
                                    print $out " -$varHash{$auxVarName} -$varHash{$auxBitName}    0\n";
                                    if ( $debug == 1 ){
                                        print " -$varHash{$auxVarName} -$varHash{$auxBitName}    0\n";
                                    }
                                }
                                else{
                                    print $out " -$varHash{$auxVarName} $varHash{$auxBitName}    0\n";
                                    if ( $debug == 1 ){
                                        print " -$varHash{$auxVarName} $varHash{$auxBitName}    0\n";
                                    }
                                }
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_OuterAdj++;
                            }
                        }
                    }
                    elsif ( $encodeEnable == 6 ){ # Commander Mode
                        if ( $debug == 1){
                            print "a    Commander Encoding (Outer Adj)\n";
                        }
                        my $numGroup = ceil( ($numNets) / $commandDivideParam ); # we can select the number of group depending on the performance.
                        my $numPerGroup = ceil(($numNets) / $numGroup);

                        ##### Auxiliary Variable Generation ##########3
                        my $auxVarName = ""; 
                        my $numCommander = 0;
                        for my $i (0 .. $numGroup-1){
                            $auxVarName = "N_c".$i."(".$eDest.")";
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;
                                $numCommander++;

                                if ($debug == 1){
                                    print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }     
                        ######################################
                        ######################################
                        my $groupIndex = -1; my $groupIndexPrev = -1;
                        #### 1st Level Commander ALO #####
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int( $i / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = ($numNets-1);
                                }

                                if( $groupIndex == 0 ){ 
                                    $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                    if( exists($varHash{$auxVarName})){
                                        print $out " -$varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                }
                                else { ### Group Index is not initial
                                    print $out "    0\n";   ## End for previous clause
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_OuterAdj++;
                                    
                                    $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                    if( exists($varHash{$auxVarName})){
                                        print $out " -$varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                }
                            }
                            my $auxNetVariable = "N".$nets[$i]."(".$eDest.")";
                            if ( exists ($varHash{$auxNetVariable} )){
                                print $out " $varHash{$auxNetVariable}";
                                $groupIndexPrev = $groupIndex;
                            }
                            else{
                                print "ERROR : There is no Net Varaible in the Hash Table\n";
                                exit(-1);
                            }
                            
                            if( $i == ($numNets-1) ){  #last Element
                                print $out "    0\n";
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_OuterAdj++;
                                
                                last;
                            }
                        }
                        #### 1st Level Commander AMO #####
                        for my $i (0 .. $numNets-1){
                            $groupIndex = int( $i / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= ($numNets-1) ){ # The Last Group
                                    $endIndex = $numNets-1;
                                }

                                $auxVarName = "N_c".$groupIndex."(".$eDest.")";
                                if( exists($varHash{$auxVarName})){
                                    for my $j ($startIndex .. $endIndex){
                                        my $auxNetVariable = "N".$nets[$j]."(".$eDest.")";
                                        print $out " $varHash{$auxVarName} -$varHash{$auxNetVariable}  0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_OuterAdj++;
                                    }
                                    # Other member of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        my $auxNetVariable_j = "N".$nets[$j]."(".$eDest.")";
                                        for my $k ($j+1 .. $endIndex){
                                            my $auxNetVariable_k = "N".$nets[$k]."(".$eDest.")";
                                            print $out " -$varHash{$auxNetVariable_j} -$varHash{$auxNetVariable_k}    0\n";
                                            $numClauses++;
                                            $numClauses_EUV++;
                                            $numClauses_EUV_OuterAdj++;
                                        }
                                    }
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                            $groupIndexPrev = $groupIndex;
                            if( $i == $numNets-1 ){  #last Element
                                last;
                            }
                        }
                        ############## End 1st Commander EO #########################
                        
                        ### Commander Iterative Generation ###
                        ### Higher Level AMO ###
                        my $commanderStart = 0; my $commanderEnd = $numCommander-1; my $extraNumCommander = $numCommander;
                        while ( $extraNumCommander > $AtLeastVariable){
                            $numGroup = ceil($extraNumCommander / $commandDivideParam );
                            $numPerGroup = ceil($extraNumCommander / $numGroup);
                            
                            ######### Auxiliary Variable Generation #############
                            $extraNumCommander = 0; # Re-initializing
                            for my $i (0 .. $numGroup-1){
                                $auxVarName = "N_c".$numCommander."(".$eDest.")";
                                if( exists($varHash{$auxVarName})) {
                                    next;
                                }
                                else{ # Add to the var Hash
                                    $varHash{$auxVarName} = $varIndex;
                                    $varIndex++;
                                    $numVarNet++;
                                    $numCommander++;

                                    $extraNumCommander++;

                                    if ($debug == 1){
                                       print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                    }
                                }
                            }
                            ####### EO -> ALO ^ AMO ########
                            $groupIndex = -1; $groupIndexPrev = -1; 
                            for my $i ($commanderStart .. $commanderEnd){
                                $groupIndex = int( ($i - $commanderStart) / $numPerGroup);             
                                if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                    my $startIndex = $i; 
                                    my $endIndex = $i+$numPerGroup-1;
                                    if ( $endIndex >= $commanderEnd ){ # The Last Group
                                        $endIndex = $commanderEnd;
                                    }
                                    
                                    my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                    my $newCommandname = "N_c".$newCommandIndex."(".$eDest.")";
                                    if ( exists($varHash{$newCommandname}) ){
                                        print $out " -$varHash{$newCommandname}";
                                   }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);

                                    }
                                    for my $j ($startIndex .. $endIndex){ 
                                        $auxVarName = "N_c".$j."(".$eDest.")";
                                        if( exists($varHash{$auxVarName})){
                                            print $out " $varHash{$auxVarName}";
                                        }
                                        else{
                                            print "ERROR - There is no command variable in Hash Table\n";
                                            exit(-1);
                                        }
                                    } 
                                    ###################
                                    print $out "    0\n";
                                    $numClauses++;
                                    $numClauses_EUV++;
                                    $numClauses_EUV_OuterAdj++;

                                }
                                $groupIndexPrev = $groupIndex;
                            }
                            ############# higher Level AMO #############
                            $groupIndex = -1; $groupIndexPrev = -1; 
                            for my $i ($commanderStart .. $commanderEnd){
                                $groupIndex = int( ($i - $commanderStart) / $numPerGroup);
                                if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                    my $startIndex = $i; 
                                    my $endIndex = $i+$numPerGroup-1;
                                    if ( $endIndex >= $commanderEnd ){ # The Last Group
                                        $endIndex = $commanderEnd;
                                    }
                                    
                                    my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                    my $newCommandname = "N_c".$newCommandIndex."(".$eDest.")";

                                    # With new Commander 
                                    for my $j ($startIndex .. $endIndex){
                                        $auxVarName = "N_c".$j."(".$eDest.")";
                                        print $out " $varHash{$newCommandname} -$varHash{$auxVarName}   0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_OuterAdj++;
                                    }
                                    # Other members of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        $auxVarName = "N_c".$j."(".$eDest.")";

                                        if ( exists($varHash{$auxVarName}) ){                                    
                                            for my $k ($j+1 .. $endIndex){
                                                my $auxCommanderName = "N_c".$k."(".$eDest.")";

                                                print $out " -$varHash{$auxVarName} -$varHash{$auxCommanderName}    0\n";
                                                $numClauses++;
                                                $numClauses_EUV++;
                                                $numClauses_EUV_OuterAdj++;
                                            }
                                        }
                                        else{
                                            print "ERROR - there is no commander variable in the hash table\n";
                                            exit(-1);
                                        }
                                    }
                                }
                                $groupIndexPrev = $groupIndex;
                            }

                            $commanderStart = $commanderEnd + 1;
                            $commanderEnd = $commanderStart + $extraNumCommander - 1;

                        }

                        # Pair-wise
                        my $commanderNameStart = ""; my $commanderNameEnd = "";
                        for my $i ($commanderStart .. $commanderEnd-1){
                            $commanderNameStart = "N_c".$i."(".$eDest.")";
                            if (exists($varHash{$commanderNameStart})){
                                for my $j ($i+1 .. $commanderEnd){
                                    $commanderNameEnd = "N_c".$j."(".$eDest.")";
                                    if (exists($varHash{$commanderNameEnd})){
                                        print $out " -$varHash{$commanderNameStart} -$varHash{$commanderNameEnd}    0\n";
                                        $numClauses++;
                                        $numClauses_EUV++;
                                        $numClauses_EUV_OuterAdj++;
                                    }
                                    else{
                                        print "ERROR - There is no commander variable in the Hash Table\n";
                                        exit(-1);
                                    }
                                }
                            }
                            else{
                                print "ERROR - There is no commander variable in the Hash Table\n";
                                exit(-1);
                            }
                        }

                    }
                    else{
                        print "ERROR in your encoding enable mode when EUV process.($encodeEnable) \n\n";
                        exit (-1);
                    }
                }
            }

            ############### Source or Sink Case ####################
            #### The Net including the pint -> EO Constraint , Other Nets -> Set by 0

            elsif ($isSource == 1 && $isSink == 0 && $isOuterPinAdj == 0 && $isInnerPinAdj == 0) {

                print $out "c EUV-SS-Source($eDest)\n";

                #### Skip below procedure ###
                my $sourceP;
                $sourceP = $1 while $undirectedEdges[0] =~ /N\S+_E\((\S+)\)\(\S+\)/g;
                foreach my $key (keys %edgesNet) {
                    if ($key eq $pins{$sourceP}[1]) {
                        next;
                    }
                    # Unit Clauses
                    for my $i (0 .. $#{$edgesNet{$key}}) {
                        print $out " -$varHash{$edgesNet{$key}[$i]}    0\n";
                        $numClauses++;
                        $numClauses_EUV++;
                        $numClauses_EUV_SS++; 
                    }
                }
            }
            elsif ($isSource == 0 && $isSink == 1 && $isOuterPinAdj == 0 && $isInnerPinAdj == 0) {

                print $out "c EUV-SS-Sink($eDest)\n";
                my $sinkP;
                $sinkP = $1 while $undirectedEdges[0] =~ /N\S+_E\(\S+\)\((\S+)\)/g;
                foreach my $key (keys %edgesNet) {
                    if ($key eq $pins{$sinkP}[1]) {
                        for my $i (0 .. $#{$edgesNet{$key}}) {
                            print $out " $varHash{$edgesNet{$key}[$i]}";
                        }
                        print $out "    0\n";
                        $numClauses++;
                        $numClauses_EUV++;
                        $numClauses_EUV_SS++;
                    }
                }
                foreach my $key (keys %edgesNet) {
                    if ($key eq $pins{$sinkP}[1]) {
                        for my $i (0 .. $#{$edgesNet{$key}}-1) {
                            for my $j ($i+1 .. $#{$edgesNet{$key}}) {
                                print $out " -$varHash{$edgesNet{$key}[$i]} -$varHash{$edgesNet{$key}[$j]}   0\n";
                                $numClauses++;
                                $numClauses_EUV++;
                                $numClauses_EUV_SS++;
                            }
                        }
                    }
                }
                foreach my $key (keys %edgesNet) {
                    if ($key eq $pins{$sinkP}[1]) {
                        next;
                    }
                    for my $i (0 .. $#{$edgesNet{$key}}) {
                        print $out " -$varHash{$edgesNet{$key}[$i]}    0\n";
                        $numClauses++;
                        $numClauses_EUV++;
                        $numClauses_EUV_SS++;
                    }
                }
            }
            else {
                print "ERROR in your ILP02 sets. $isSource $isSink $isOuterPinAdj $isInnerPinAdj\n\n";
                exit (-1);
            }
        }
    }
    elsif ($infileStatus == 3) {

        if ($isLogPrinted == 0 ) {
            print "a     3. Edge assignment for each edge for every net.\n";
            print $out "c 3. Edge assignment for each edge for every net.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP03";
        $isFeasible = 0;
        if ($line =~ />=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /N\S+_E\((\S+)\)\((\S+)\)/) {
                $edgeOrig = $1;
                $edgeDest = $2;
                if (exists($h_sources{$edgeDest})){
                    $isFeasible = 0;
                    @signsILP = ("i");
                }
                elsif (exists($h_sinks{$edgeOrig})){
                    $isFeasible = 0;
                    @signsILP = ("i");
                }
                else {
                    $isFeasible = 1;
                    @signsILP = ("x");
                }
            }

            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Process Un-Directed Edges Only
            @undirectedEdges = ();
            %h_undirectedEdges = ();
            for my $e (0 .. $#termsILP) {
                $termsILP[$e] =~ m/^\S+E\((\S+)\)\((\S+)\)$/;
                my $eOrig = $1;
                my $eDest = $2;
                if ($termsILP[$e] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                    if ($1 < $4 || $2 < $5 || $3 < $6) {
                        push @undirectedEdges, $termsILP[$e];
                        $h_undirectedEdges{$termsILP[$e]} = 1;
                    }
                    else {
                        $isFeasible = 0;
                    }
                } 
                elsif (exists($h_sources{$eOrig})){
                    push @undirectedEdges, $termsILP[$e];
					$h_undirectedEdges{$termsILP[$e]} = 1;
                }
                elsif (exists($h_sinks{$eDest})){
                    push @undirectedEdges, $termsILP[$e];
					$h_undirectedEdges{$termsILP[$e]} = 1;
                }
                else {
                    $isFeasible = 0;
                }
            } 

            if ($isFeasible == 0) {
                next;
            }

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}   ";
                    if (exists($h_undirectedEdges{$term})){
                        print $out "V";
                    }
                    print $out "\n";
                }
            }

            if ($isFeasible == 1) {
                print $out " $varHash{$termsILP[0]} -$varHash{$termsILP[1]}    0\n";
                $numClauses++;
            }
            else {
                print "ERROR in your ILP03 sets.\n\n";
                exit (-1);
            }
        }
    }
    elsif ($infileStatus == 4) {
        if ($isLogPrinted == 0 ) {
            print "a     4. Exclusiveness use of each edge + Metal segment assignment by using edge usage information.\n";
            print $out "c 4. Exclusiveness use of each edge + Metal segment assignment by using edge usage information.\n";
            $isLogPrinted = 1;
        }

        $ilpset = "ILP04";
        $isSource = 0;
        $isSink = 0;
        my $termOrig = "";
        my $termDest = "";
        if ($line =~ /=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /M\((\S+)\)\((\S+)\)/) {
                $edgeOrig = $1;
                $edgeDest = $2;
                if (exists($h_sources{$edgeOrig})){
                    $isSource = 1;
                    $isSink = 0;
                    @signsILP = ("s");
                }
                elsif (exists($h_sinks{$edgeDest})){
                    $isSource = 0;
                    $isSink = 1;
                    @signsILP = ("t");
                }
                else {
                    $isSource = 0;
                    $isSink = 0;
                    @signsILP = ("x");
                }
            }

            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Collect Un-Directed Edges Only
            @undirectedEdges = ();
            %h_undirectedEdges = ();
            for my $e (1 .. $#termsILP) {
                $termsILP[$e] =~ m/^\S+E\((\S+)\)\((\S+)\)$/;
                my $eOrig = $1;
                my $eDest = $2;
                if ($termsILP[$e] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                    if ($1 < $4 || $2 < $5 || $3 < $6) {
                        push @undirectedEdges, $termsILP[$e];
						$h_undirectedEdges{$termsILP[$e]} = 1;
                    }
                } 
                elsif (exists($h_sources{$eOrig})){
                    push @undirectedEdges, $termsILP[$e];
					$h_undirectedEdges{$termsILP[$e]} = 1;
                }
                elsif (exists($h_sinks{$eDest})){
                    push @undirectedEdges, $termsILP[$e];
					$h_undirectedEdges{$termsILP[$e]} = 1;
                }
            } 

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}   ";
                    if (exists($h_undirectedEdges{$term})){
                        print $out "V";
                    }
                    print $out "\n";
                }
            }

            if ($isSource == 0 || $isSink == 0) {
                #ALO is common
                print $out " -$varHash{$termsILP[0]}";
                for my $i (0 .. $#undirectedEdges) {
                    print $out " $varHash{$undirectedEdges[$i]}";
                }
                print $out "    0\n";
                $numClauses++;
                $numClauses_MS++;

                #AMO is divied by the mode
                if ( ($encodeEnable <= 3) || ($#undirectedEdges <= (($AtLeastVariable - 1) * 2)) ){ # Pair-wise Encoding
                    for my $i (0 .. $#undirectedEdges) {
                        print $out " $varHash{$termsILP[0]} -$varHash{$undirectedEdges[$i]}    0\n";
                        $numClauses++;
                        $numClauses_MS++;
                    }
                    for my $i (0 .. $#undirectedEdges-1) {
                        for my $j ($i+1 .. $#undirectedEdges) {
                            print $out " -$varHash{$undirectedEdges[$i]} -$varHash{$undirectedEdges[$j]}    0\n";
                            $numClauses++;
                            $numClauses_MS++;
                        }
                    }
                }
                elsif ( $encodeEnable <= 6 ){  #### Commander Encoding
                    print "a        MS - Commander Encoding\n";
                    if ( $debug == 1 ){
                    }
                    my $numGroup = ceil(($#undirectedEdges + 2) / $commandDivideParam ); # we can select the number of group depending on the performance. + Add 1 Commander Variable
                    my $numPerGroup = ceil(($#undirectedEdges + 2) / $numGroup); 

                    ##### AMO { -MS U {Edge Set: #Net} } : #Net + 1
                    ##### Auxiliary Variable Generation ##########3
                    my $auxVarName = ""; 
                    my $numCommander = 0;

                    for my $i (0 .. $numGroup-1){
                        $auxVarName = "C".$i."_".$termsILP[0];
                        if( exists($varHash{$auxVarName})) {
                            next;
                        }
                        else{ # Add to the var Hash
                            $varHash{$auxVarName} = $varIndex;
                            $varIndex++;
                            $numVarNet++;
                            $numCommander++;

                            if ($debug == 1){
                                print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                            }
                        }
                    }     

                    #### EO : ALO ( {-C) U Group )
                    my $groupIndex = -1; my $groupIndexPrev = -1;

                    #### 1st Level Commander ALO #####
                    for my $i (0 .. $#undirectedEdges){
                        $groupIndex = int( ($i + 1) / $numPerGroup);  # First Group is inclduing Metal Segment Variable
                        if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                            my $startIndex = $i; 
                            my $endIndex = $i+$numPerGroup-1;
                            if ( $endIndex >= $#undirectedEdges ){ # The Last Group
                                $endIndex = $#undirectedEdges;
                            }

                            if( $groupIndex == 0 ){ # Metal Segment is inthe first group
                                $auxVarName = "C".$groupIndex."_".$termsILP[0];  # Command
                                if( exists($varHash{$auxVarName})){
                                    print $out " -$varHash{$auxVarName}";
                                    print $out " -$varHash{$termsILP[0]}";  # Metal Segment  
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                            else { ### Group Index is not initial
                                print $out "    0\n";   ## End for previous clause
#                               print "     0\n";
                                $numClauses++;
                                $numClauses_MS++;

                                
                                $auxVarName = "C".$groupIndex."_".$termsILP[0];  # Command
                                if( exists($varHash{$auxVarName})){
                                    print $out " -$varHash{$auxVarName}";
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                        }
                        print $out " $varHash{$undirectedEdges[$i]}";
                        $groupIndexPrev = $groupIndex;

                        if( $i == $#undirectedEdges ){  #last Element
                            print $out "    0\n";
                            $numClauses++;
                            $numClauses_MS++;

                            last;
                        }
                    }

                    #### 1st Level Commander AMO #####
                    for my $i (0 .. $#undirectedEdges){
                        $groupIndex = int( ($i + 1) / $numPerGroup);  # First Group is inclduing Metal Segment Variable
                        if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                            my $startIndex = $i; 
                            my $endIndex = $i+$numPerGroup-1;
                            if ( $endIndex >= $#undirectedEdges ){ # The Last Group
                                $endIndex = $#undirectedEdges;
                            }

                            if( $groupIndex == 0 ){ # Metal Segment is in the first group
                                $endIndex -= 1;  # First Group is including Metal Segment
                                
                                $auxVarName = "C".$groupIndex."_".$termsILP[0];  # Command
                                if( exists($varHash{$auxVarName})){
                                    # Commander and Metal Segment : Pairwise
                                    print $out " $varHash{$auxVarName} $varHash{$termsILP[0]}    0\n";
                                    $numClauses++;
                                    $numClauses_MS++;
                                    for my $j ($startIndex .. $endIndex){
                                        print $out " $varHash{$auxVarName} -$varHash{$undirectedEdges[$j]}  0\n";
                                        $numClauses++;
                                        $numClauses_MS++;
                                    }
                                    # Metal Segment : Pairwise
                                    for my $j ($startIndex .. $endIndex){
                                        print $out " $varHash{$termsILP[0]} -$varHash{$undirectedEdges[$j]}  0\n";
                                        $numClauses++;
                                        $numClauses_MS++;
                                    }
                                    # Other member of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        for my $k ($j+1 .. $endIndex){
                                            print $out " -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}    0\n";
                                            $numClauses++;
                                            $numClauses_MS++;
                                        }
                                    }
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }

                            }
                            else { ### Group Index is not initial    
                                $auxVarName = "C".$groupIndex."_".$termsILP[0];  # Command
                                if( exists($varHash{$auxVarName})){
                                    # Commander and : Pairwise
                                    for my $j ($startIndex .. $endIndex){
                                        print $out " $varHash{$auxVarName} -$varHash{$undirectedEdges[$j]}  0\n";
                                        $numClauses++;
                                        $numClauses_MS++;
                                   }
                                    # Other member of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        for my $k ($j+1 .. $endIndex){
                                            print $out " -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}    0\n";
                                            $numClauses++;
                                            $numClauses_MS++;
                                        }
                                    }
                                }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);
                                }
                            }
                        }
                        $groupIndexPrev = $groupIndex;

                        if( $i == $#undirectedEdges ){  #last Element
                            last;
                        }
                       
                    }
                    ############## End 1st Commander EO #########################
                    ###### AMO for Commander ##### Keep the Pairwise if # Commander <= 6
                    my $commanderStart = 0; my $commanderEnd = $numCommander-1; my $extraNumCommander = $numCommander;
                    while ( $extraNumCommander > $AtLeastVariable){
                        $numGroup = ceil($extraNumCommander / $commandDivideParam );
                        $numPerGroup = ceil($extraNumCommander / $numGroup);
                        
                        ######### Auxiliary Variable Generation #############
                        $extraNumCommander = 0; # Re-initializing
                        for my $i (0 .. $numGroup-1){
                            $auxVarName = "C".$numCommander."_".$termsILP[0];
                            if( exists($varHash{$auxVarName})) {
                                next;
                            }
                            else{ # Add to the var Hash
                                $varHash{$auxVarName} = $varIndex;
                                $varIndex++;
                                $numVarNet++;
                                $numCommander++;

                                $extraNumCommander++;

                                if ($debug == 1){
                                    print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                                }
                            }
                        }
                        ####### EO -> ALO ^ AMO ########
                        $groupIndex = -1; $groupIndexPrev = -1; 
                        for my $i ($commanderStart .. $commanderEnd){
                            $groupIndex = int( ($i - $commanderStart) / $numPerGroup);             
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= $commanderEnd ){ # The Last Group
                                    $endIndex = $commanderEnd;
                                }
                                
                                my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                my $newCommandname = "C".$newCommandIndex."_".$termsILP[0];
                                if ( exists($varHash{$newCommandname}) ){
                                    print $out " -$varHash{$newCommandname}";
                               }
                                else{
                                    print "ERROR - There is no command variable in Hash Table\n";
                                    exit(-1);

                                }
                                for my $j ($startIndex .. $endIndex){ 
                                    $auxVarName = "C".$j."_".$termsILP[0];
                                    if( exists($varHash{$auxVarName})){
                                        print $out " $varHash{$auxVarName}";
                                    }
                                    else{
                                        print "ERROR - There is no command variable in Hash Table\n";
                                        exit(-1);
                                    }
                                } 
                                ###################
                                print $out "    0\n";
                                $numClauses++;
                                $numClauses_MS++;

                            }
                            $groupIndexPrev = $groupIndex;
                        }
                        ############# higher Level AMO #############
                        $groupIndex = -1; $groupIndexPrev = -1; 
                        for my $i ($commanderStart .. $commanderEnd){
                            $groupIndex = int( ($i - $commanderStart) / $numPerGroup);
                            if ( $groupIndexPrev != $groupIndex ) {  ## When Group Index is changing... 
                                my $startIndex = $i; 
                                my $endIndex = $i+$numPerGroup-1;
                                if ( $endIndex >= $commanderEnd ){ # The Last Group
                                    $endIndex = $commanderEnd;
                                }
                                
                                my $newCommandIndex = $commanderEnd + $groupIndex + 1;
                                my $newCommandname = "C".$newCommandIndex."_".$termsILP[0];

                                # With new Commander 
                                for my $j ($startIndex .. $endIndex){
                                    $auxVarName = "C".$j."_".$termsILP[0];
                                    print $out " $varHash{$newCommandname} -$varHash{$auxVarName}   0\n";
                                    $numClauses++;
                                    $numClauses_MS++;

                                }
                                # Other members of group
                                for my $j ($startIndex .. $endIndex-1){
                                    $auxVarName = "C".$j."_".$termsILP[0];
                                    for my $k ($j+1 .. $endIndex){
                                        my $auxCommanderName = "C".$k."_".$termsILP[0];
                                        print $out " -$varHash{$auxVarName} -$varHash{$auxCommanderName}    0\n";
                                        $numClauses++;
                                        $numClauses_MS++;

                                    }
                                }
                            }
                            $groupIndexPrev = $groupIndex;
                        }

                        $commanderStart = $commanderEnd + 1;
                        $commanderEnd = $commanderStart + $extraNumCommander - 1;
                    }
                    # Pair-wise
                    my $commanderNameStart = ""; my $commanderNameEnd = "";
                    for my $i ($commanderStart .. $commanderEnd-1){
                        $commanderNameStart = "C".$i."_".$termsILP[0];
                        if (exists($varHash{$commanderNameStart})){
                            for my $j ($i+1 .. $commanderEnd){
                                $commanderNameEnd = "C".$j."_".$termsILP[0];
                                if (exists($varHash{$commanderNameEnd})){
                                    print $out " -$varHash{$commanderNameStart} -$varHash{$commanderNameEnd}    0\n";
                                    $numClauses++;
                                    $numClauses_MS++;
                                }
                                else{
                                    print "ERROR - There is no commander variable in the Hash Table\n";
                                    exit(-1);
                                }
                            }
                        }
                        else{
                            print "ERROR - There is no commander variable in the Hash Table\n";
                            exit(-1);
                        }
                    }
                }
                elsif ( $encodeEnable == 7 ){
                    if ( $debug == 1 ){
                        print $out "c   MS: Bimander Encoding\n";
                    }
                    my $numGroup = ceil(($#undirectedEdges+2) / $bimanderDivideParam ); # Metal Segment is including the number of variable.
                    my $numPerGroup = ceil(($#undirectedEdges+2) / $numGroup); 
                    my $numBitGroup = ceil(log($numGroup)/log(2));

                    my $auxVarName = ""; 
                    for my $i (0 .. $numBitGroup-1){
                        $auxVarName = "B".$i."_".$termsILP[0];
                        if( exists($varHash{$auxVarName})) {
                            next;
                        }
                        else{ # Add to the var Hash
                            $varHash{$auxVarName} = $varIndex;
                            $varIndex++;
                            $numVarNet++;

                            if ($debug == 1){
                               print "a            $auxVarName := $varHash{$auxVarName}    V is added\n";
                            }
                        }
                    }
                    my $groupIndex = -1; my $groupIndexPrev = -1; my $lastGroup = 0;
                    for my $i (0 .. $#undirectedEdges){
                        $groupIndex = int(($i + 1) / $numPerGroup);
                        ############## 1st Step : Execute Group AMO ################
                        if( $groupIndexPrev != $groupIndex ){
                            my $startIndex = $i; 
                            my $endIndex = $i+$numPerGroup-1;
                            if ( $endIndex >= $#undirectedEdges ){ # The Last Group
                                $endIndex = $#undirectedEdges;
                                $lastGroup = 1;
                            }
                            if ( $groupIndex == 0 ){ # Metal Segment is in the First Group index. 
                                $endIndex -= 1; # Metal Segment
                            
                                if( exists($varHash{$termsILP[0]}) ){
                                    # Metal Segment : Pairwise
                                    for my $j ($startIndex .. $endIndex){
                                        print $out " $varHash{$termsILP[0]} -$varHash{$undirectedEdges[$j]}  0\n";
                                        $numClauses++;
                                        $numClauses_MS++;

                                        if ( $debug == 1){
                                            print "a            $varHash{$termsILP[0]}($termsILP[0]) -$varHash{$undirectedEdges[$j]}($undirectedEdges[$j])    0\n";
                                        }
                                    }

                                    # Other member of group
                                    for my $j ($startIndex .. $endIndex-1){
                                        for my $k ($j+1 .. $endIndex){
                                            print $out " -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}    0\n";
                                            if ( $debug == 1 ){
                                                print "a           -$varHash{$undirectedEdges[$j]}($undirectedEdges[$j]) -$varHash{$undirectedEdges[$k]}($undirectedEdges[$k])    0\n";
                                            }
                                            $numClauses++;
                                            $numClauses_MS++;
                                        }   
                                    }
                                }
                                else{
                                    print "ERROR - There is no metal segment variable in the hash table\n";
                                    exit(-1);
                                }
                            }
                            else{  # Group Index is not the first
                                # Other member of group
                                for my $j ($startIndex .. $endIndex-1){
                                    for my $k ($j+1 .. $endIndex){
                                        print $out " -$varHash{$undirectedEdges[$j]} -$varHash{$undirectedEdges[$k]}    0\n";
                                        if ( $debug == 1 ){
                                            print "a            -$varHash{$undirectedEdges[$j]}($undirectedEdges[$j]) -$varHash{$undirectedEdges[$k]}($undirectedEdges[$k])    0\n";
                                        }
                                        $numClauses++;
                                        $numClauses_MS++;
                                    }
                                }
                            }
                        }
                        $groupIndexPrev = $groupIndex;
                        if ($lastGroup == 1){
                            last;
                        }
                    }

                    ################# 2nd Step : bimander Clauses #########################
                    ### For Metal Segment Variable
                    for my $i (0 .. $numBitGroup-1){
                        $auxVarName = "B".$i."_".$termsILP[0];
                        if( exists($varHash{$auxVarName}) ){
                            print $out " $varHash{$termsILP[0]} -$varHash{$auxVarName}  0\n";
                            $numClauses++;
                            $numClauses_MS++;

                            if ( $debug == 1 ){
                                print "a            $varHash{$termsILP[0]}($termsILP[0]) -$varHash{$auxVarName}($auxVarName)    0\n";
                            }
                        }
                        else{
                            print "ERROR in var Hash. There is no bimander variable..\n\n";
                            exit (-1);
                        }
                    }

                    my $groupIndex = -1;
                    for my $i (0 .. $#undirectedEdges){
                        $groupIndex = int(($i+1) / $numPerGroup);
                        my $remainder = -1;

                        for my $j (0 .. $numBitGroup-1){
                            $remainder = int($groupIndex % $bimanderDivideParam);
                            $groupIndex = int($groupIndex / $bimanderDivideParam);
                            $auxVarName = "B".$j."_".$termsILP[0];
                            if( exists($varHash{$auxVarName})) {
                                if ($remainder == 0){
                                    print $out " -$varHash{$undirectedEdges[$i]} -$varHash{$auxVarName}    0\n";
                                    if ( $debug == 1 ){
                                        print "a            -$varHash{$undirectedEdges[$i]}($undirectedEdges[$i]) -$varHash{$auxVarName}($auxVarName)    0\n";
                                    }
                                }
                                else{
                                    print $out " -$varHash{$undirectedEdges[$i]} $varHash{$auxVarName}    0\n";
                                    if ( $debug == 1 ){
                                        print "a            -$varHash{$undirectedEdges[$i]}($undirectedEdges[$i]) $varHash{$auxVarName}($auxVarName)     0\n";
                                    }
                                }
                                $numClauses++;
                                $numClauses_MS++;
                            }
                            else{
                                print "ERROR in var Hash. There is no bimander variable..\n\n";
                                exit (-1);
                            }
                        }
                    }
                }
                else{
                    print "ERROR - Abnormal encoding Mode ($encodeEnable)\n";
                    exit(-1);
                }
            }
            else {
                print "ERROR in your ILP04 sets.\n\n";
                exit (-1);
            }
        }
    }
    elsif ($infileStatus == 5) {

        if ($isLogPrinted == 0 ) {
            print "a     5. Wire assignment by using commodity flow information.\n";
            print $out "c 5. Wire assignment by using commodity flow information.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP05";
        if ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;

            if ($wireEnable == 1){  # Wire Segment Enable
                @tempArr = split /[\=\>\<\s]+/, $line;
                if ($tempArr[0] =~ /W\(\S+\)\(\S+\)/) {
                    @signsILP = ("x");
                }

                ### Collect ILP Terms and Signs in LHS
                @termsILP = ($tempArr[0]);
                for (my $i=2; $i<$#tempArr; $i+=2) {
                    if ($tempArr[$i-1] eq "+") {
                        push @termsILP, $tempArr[$i];
                        push @signsILP, "+";
                    }
                    elsif ($tempArr[$i-1] eq "-") {
                        push @termsILP, $tempArr[$i];
                        push @signsILP, "-";
                    }
                }
                $numILPterms = scalar @termsILP;
                $signsPattern = join "", @signsILP;

                ### Collect Un-Directed Edges Only
                @undirectedEdges = ();
                %h_undirectedEdges = ();
                for my $e (1 .. $#termsILP) {
                    $termsILP[$e] =~ m/^\S+E\((\S+)\)\((\S+)\)$/;
                    my $eOrig = $1;
                    my $eDest = $2;
                    if ($termsILP[$e] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                        if ($1 < $4 || $2 < $5 || $3 < $6) {
                            push @undirectedEdges, $termsILP[$e];
							$h_undirectedEdges{$termsILP[$e]} = 1;
                        }
                    } 
                    elsif (exists($h_sources{$eOrig})){
                        push @undirectedEdges, $termsILP[$e];
						$h_undirectedEdges{$termsILP[$e]} = 1;
                    }
                    elsif (exists($h_sinks{$eDest})){
                        push @undirectedEdges, $termsILP[$e];
						$h_undirectedEdges{$termsILP[$e]} = 1;
                    }
                } 

                ### Print ILP Term as Indices in Comment
                if ($debug == 1) {
                    print $out "c   Pattern := $signsPattern\n";
                    foreach my $term (@termsILP) {
                        print $out "c     $term := $varHash{$term}   ";
                        if ($term ~~ @undirectedEdges) {
                            print $out "V";
                        }
                        print $out "\n";
                    }
                }

                print $out " -$varHash{$termsILP[0]}";
                for my $i (0 .. $#undirectedEdges) {
                    print $out " $varHash{$undirectedEdges[$i]}";
                }
                print $out "    0\n";
                $numClauses++;
                for my $i (0 .. $#undirectedEdges) {
                    print $out " $varHash{$termsILP[0]} -$varHash{$undirectedEdges[$i]}    0\n";
                    $numClauses++;
                }
            }
        }
        elsif ($line =~ />=/) {
            if ($debug == 1) {
                    print $out "c   ILP const eq.$numConstraints:    $line\n";
                    print $out "c   ILP const eq.$numConstraints does NOT need to be SAT.\n";
            }
            $numConstraints++;
        }
    }
    elsif ($infileStatus == 6) {

        if ($isLogPrinted == 0 ) {
            print "a     6. Geometry variables for Left (GL), Right (GR), Front (GF), and Back (GB) directions.\n";
            print $out "c 6. Geometry variables for Left (GL), Right (GR), Front (GF), and Back (GB) directions.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP06";
        if ($line =~ />=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /G(\w)_V/) {
                $adj = $1;
                if ($adj eq "L") {
                    @signsILP = ("l");
                }
                elsif ($adj eq "R") {
                    @signsILP = ("r");
                }
                elsif ($adj eq "F") {
                    @signsILP = ("f");
                }
                elsif ($adj eq "B") {
                    @signsILP = ("b");
                }
            }

            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}\n";
                }
            }

            ## For Converting from reduced ILP constraints
            if ( $numILPterms == 2 ){       #### termsILP[0] = termsILP[1] #####
                if (($signsILP[0] eq "l") || ($signsILP[0] eq "f") || ($signsILP[0] eq "r") || ($signsILP[0] eq "b")) {
                    print $out " $varHash{$termsILP[0]} -$varHash{$termsILP[1]}     0\n";
                    $numClauses++;
                    $numClauses_GV++;
                    print $out " -$varHash{$termsILP[0]} $varHash{$termsILP[1]}     0\n";
                    $numClauses++;
                    $numClauses_GV++;
                }
                else {
                    print "ERROR in your ILP06 sets (2 literals).\n\n";
                    exit (-1);
                }
            }
            else{
                if (($signsILP[0] eq "l") || ($signsILP[0] eq "f")) {
                    print $out " $varHash{$termsILP[0]} $varHash{$termsILP[1]} -$varHash{$termsILP[2]}    0\n";
                    $numClauses++;
                    $numClauses_GV++;
                    print $out " -$varHash{$termsILP[0]} $varHash{$termsILP[2]}    0\n";
                    $numClauses++;
                    $numClauses_GV++;
                    print $out " -$varHash{$termsILP[0]} -$varHash{$termsILP[1]}    0\n";
                    $numClauses++;
                    $numClauses_GV++;

                }
                elsif (($signsILP[0] eq "r") || ($signsILP[0] eq "b")) {
                    print $out " $varHash{$termsILP[0]} -$varHash{$termsILP[1]} $varHash{$termsILP[2]}    0\n";
                    $numClauses++;
                    $numClauses_GV++;

                    print $out " -$varHash{$termsILP[0]} -$varHash{$termsILP[2]}    0\n";
                    $numClauses++;
                    $numClauses_GV++;

                    print $out " -$varHash{$termsILP[0]} $varHash{$termsILP[1]}    0\n";
                    $numClauses++;
                    $numClauses_GV++;

                }
                else {
                    print "ERROR in your ILP06 sets (3 literals).\n\n";
                    exit (-1);
                }
            }
        }
        elsif ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
                print $out "c   ILP const eq.$numConstraints does NOT need to be SAT.\n";
            }
            $numConstraints++;
        }
    }
    elsif ($infileStatus == 7) {

        if ($isLogPrinted == 0 ) {
            print "a     7. Minimum Area Rule.\n";
            print $out "c 7. Minimum Area Rule.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP07";
        if ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /G(\w)_V/) {
                @signsILP = ("g");
            }

            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}\n";
                }
            }

            for my $i (0 .. $#termsILP-1) {
                for my $j ($i+1 .. $#termsILP) {
                    print $out " -$varHash{$termsILP[$i]} -$varHash{$termsILP[$j]}    0\n";
                    $numClauses++;
                }
            }
        }
    }
    elsif ($infileStatus == 8) {
        if ($isLogPrinted == 0 ) {
            print "a     8. Tip-to-Tip Spacing Rule.\n";
            print $out "c 8. Tip-to-Tip Spacing Rule.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP08";
        if ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /G(\w)_V/) {
                @signsILP = ("g");
            }

            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}\n";
                }
            }

            # Pair-wise AMO Constraint.
            for my $i (0 .. $#termsILP-1){
                for my $j ($i+1 .. $#termsILP){
                    print $out " -$varHash{$termsILP[$i]} -$varHash{$termsILP[$j]}    0\n";
                    $numClauses++;
                }
            }
        }
    }
    elsif ($infileStatus == 9) {
        if ($isLogPrinted == 0 ) {
            print "a     9. Via-to-Via Spacing Rule.\n";
            print $out "c 9. Via-to-Via Spacing Rule.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP09";
        if ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /M\(\S+\)\(\S+\)/) {
                @signsILP = ("v");
            }

            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}\n";
                }
            }

            # General Pairwise AMO
            for my $i (0 .. $#termsILP-1) {
                for my $j ($i+1 .. $#termsILP) {
                    print $out " -$varHash{$termsILP[$i]} -$varHash{$termsILP[$j]}    0\n";
                    $numClauses++;
                }
            }
        }
    }
    ################ [2019-01-09] PRL Rule
    elsif ($infileStatus == 11) {
        if ($isLogPrinted == 0 ) {
            print "a     11. Parallel Run Length Rule.\n";
            print $out "c 11. Parallel Run Length Rule.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP11";
        if ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            
            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /G(\w)_V/) {
                @signsILP = ("g");
            }
            
            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;  

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}\n";
                }
            }

            # General Pair-wise AMO Constraint.
            for my $i (0 .. $#termsILP-1){
                for my $j ($i+1 .. $#termsILP){
                    print $out " -$varHash{$termsILP[$i]} -$varHash{$termsILP[$j]}    0\n";
                    $numClauses++;
                }
            }
        }
    }
    ################ [2019-01-10] SHR Rule
   elsif ($infileStatus == 12) {
        if ($isLogPrinted == 0 ) {
            print "a     12. Step Height Rule.\n";
            print $out "c 12. Step Height Rule.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP12";
        if ($line =~ /<=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;

            @tempArr = split /[\=\>\<\s]+/, $line;
            if ($tempArr[0] =~ /G(\w)_V/) {
                @signsILP = ("g");
            }
            
            ### Collect ILP Terms and Signs in LHS
            @termsILP = ($tempArr[0]);
            for (my $i=2; $i<$#tempArr; $i+=2) {
                if ($tempArr[$i-1] eq "+") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "+";
                }
                elsif ($tempArr[$i-1] eq "-") {
                    push @termsILP, $tempArr[$i];
                    push @signsILP, "-";
                }
            }
            $numILPterms = scalar @termsILP;
            $signsPattern = join "", @signsILP;  

            ### Print ILP Term as Indices in Comment
            if ($debug == 1) {
                print $out "c   Pattern := $signsPattern\n";
                foreach my $term (@termsILP) {
                    print $out "c     $term := $varHash{$term}\n";
                }
            }

            # General Pair-wise AMO Constraint.
            for my $i (0 .. $#termsILP-1){
                for my $j ($i+1 .. $#termsILP){
                    print $out " -$varHash{$termsILP[$i]} -$varHash{$termsILP[$j]}    0\n";
                    $numClauses++;
                }
            }
        }
    }

######################################################
    elsif ($infileStatus == 10) {
        if ($isLogPrinted == 0 ) {
            print "a     10. Given Solutions, e.g., Sources, Sinks, etc.\n";
            print $out "c 10. Given Solutions, e.g., Sources, Sinks, etc.\n";
            $isLogPrinted = 1;
        }
        $ilpset = "ILP10";
        if ($line =~ /=/) {
            if ($debug == 1) {
                print $out "c   ILP const eq.$numConstraints:    $line\n";
            }
            $numConstraints++;
            @tempArr = split /[\-\=\>\<\s]+/, $line;


###################### [2018-12-17] Should be check for new lp format #######################

            #### Skipping Routing if tempArr is not in varHash
            #### Wire is not there is WireEnable is disable

            if (exists $varHash{$tempArr[0]}){
            #######################################################
                if ($tempArr[0] =~ /^\S+E\((\S+)\)\((\S+)\)$/) {
                    my $eOrig = $1;
                    my $eDest = $2;

                    if ($tempArr[0] =~ /^\S+E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)$/) {
                        if ($1 < $4 || $2 < $5 || $3 < $6) {
                            if ($tempArr[1] == 0) {
                                print $out " -$varHash{$tempArr[0]}    0\n";
                                $numClauses++;
                            }
                            elsif ($tempArr[1] == 1) {
                                print $out " $varHash{$tempArr[0]}    0\n";
                                $numClauses++;
                            }
                        }
                    } 
                    else {
                        #print "a    Unit Literal = $tempArr[0]\n";
                        ### 
                        if ($tempArr[1] == 0) {
                            print $out " -$varHash{$tempArr[0]}    0\n";
                            $numClauses++;
                        }
                        elsif ($tempArr[1] == 1) {
                            print $out " $varHash{$tempArr[0]}    0\n";
                            $numClauses++;
                        }
                    }
                }
                else {
                    if ($tempArr[1] == 0) {
                        print $out " -$varHash{$tempArr[0]}    0\n";
                        $numClauses++;
                    }
                    elsif ($tempArr[1] == 1) {
                        print $out " $varHash{$tempArr[0]}    0\n";
                        $numClauses++;
                    }
                    else {
                        next;
                    }
                }
            }
        }
    }
}
close ($in);
close ($out);


my %varHash_reverse = reverse %varHash;

############## Start should be .cnf.tmp file... ##############
my $bcpfile0 = "$outdir/$seedName".".cnf.tmp"; 
my $bcpfile1 = "$outdir/$seedName".".cnf.tmp1";
my $iterationFlag = 1;   ## 0 : Terminate Iteration , 1 : Keep Iteration
my $iterationNum = 0;

my $numUnitClausesRemoved = 0;

my %TrueUnitClause = ("NULL");
my $numTrueUnit = 0;

if ($BCPEnable == 1){ 
    print "a     Pre-. BCP (Boolean Constraint Propagation)\n";

    while ($iterationFlag == 1) { 
        print "a        Store Unit Clauses in Array and Save Target Clause in File\n";
        $iterationFlag = 0;  ## Iteration Initializing...
        $iterationNum++;

### Literal Counting and BCP ###
        open (my $in, "$bcpfile0");
        open (my $out, '>', $bcpfile1);

### Literal Count ###
        my %literals = ();
        my @literalArr = ();
        my $numUnitClause = 0;

         ################ For BCP ##########
         my %unitLiteral = ("NULL");  ### Global Position
         my $unitIndex = 0;
        
        while (<$in>) {
            my $line = $_;
            chomp($line);
            @literalArr = ();

            if ($line =~ /^c/){
                print $out "$line\n";
            }
            elsif ($line =~ /^p/){
                print $out "$line\n";
            }
            else{
                if ($line =~ /[\s\t]+0$/) {
                    $line =~ s/^[\s]+//g;
                    @literalArr = split /[\s\t]+/, $line;

                    if ($#literalArr == 1) {
                        my $key = abs(int($literalArr[0]));
                        if ( int($literalArr[0]) > 0 ){  # True Value
                            if( exists($unitLiteral{$key} )){
                                ### Add Conflict finding Routine
                                if( $unitLiteral{$key} == 0){
                                    print "Unsatisfiable!: there is conflict in the line = $line\n";
                                    exit(0);
                                }
                                else{
                                    print "a     True : Duplicated... ($key, $unitLiteral{$key})\n";
                                    next;
                                }
                            }
                            else{ 
                                $unitLiteral{$key} = 1;
                                $unitIndex++;
					
				$TrueUnitClause{$varHash_reverse{$key}} = -1;
				$numTrueUnit++;

                            }
                        }
                        else{ # False Value
                            if( exists($unitLiteral{$key} )){
                                if( $unitLiteral{$key} == 1){
                                    print "Unsatisfiable!: there is conflict in the line = $line\n";
                                    exit(0);
                                }
                                else{
                                    print "a     False : Duplicated... ($key, $unitLiteral{$key})\n";
                                    next;
                                }
                            }
                            else{
                                $unitLiteral{$key} = 0; 
                                $unitIndex++;
                            }
                        }
                    }
                    else{
                        print $out "$line\n";
                    }
                }
            }
        }
        close ($in);
        close ($out);

        print "a        #Unit Clauses = $unitIndex\n";

        ############################################################
        if ( $unitIndex == 0 ){
            last;
        }
        else{
            if ($debug == 1){
                print "a        Unit Propagation Start...\n\n";
            }
            $iterationFlag = 1;
            $numUnitClausesRemoved += $unitIndex;

            open (my $out, "$bcpfile1");
            open (my $in, '>', $bcpfile0);

            my $truncatedLine = "";
            my $deleteFlag = 0;

            while (<$out>) {
                my $line = $_;
                chomp($line);
                @literalArr = ();

                if ($line =~ /^c/){
                    print $in "$line\n";
                }
                elsif ($line =~ /^p/){
                    print $in "$line\n";
                }
                else{
                    if ($line =~ /[\s\t]+0$/) {
                        $line =~ s/^[\s]+//g;
                        @literalArr = split /[\s\t]+/, $line;

                        $deleteFlag = 0;
                        $truncatedLine = $line;
                        for my $i (0 .. $#literalArr-1){
                            if( int($literalArr[$i]) > 0 ){ ## True
                                my $key = abs($literalArr[$i]);

                                if( exists($unitLiteral{$key}) ){
                                    if ($unitLiteral{$key} == 1){ # True Assignment -> Same Assingment -> Delete(Skip) Clause
                                        $deleteFlag = 1;
                                        last;
                                    }
                                    else{  # Different Assignment -> Delete Literal Only.
                                        $truncatedLine =~ s/^${literalArr[$i]}[\s]+/ /g;
                                        $truncatedLine =~ s/[\s]+${literalArr[$i]}[\s]+/ /g;
                                        next;
                                    }
                                }
                                else{ # No Match with Unit Literal
                                    next;
                                }
                            }
                            else{  # False
                                my $key = abs($literalArr[$i]);
                                if( exists($unitLiteral{$key}) ){
                                    if ($unitLiteral{$key} == 0){ # False Assignment -> Same Assingment -> Delete(Skip) Clause
                                        $deleteFlag = 1;
                                        last;
                                    }
                                    else{  # Different Assignment -> Delete Literal Only.
                                        $truncatedLine =~ s/^${literalArr[$i]}[\s]+/ /g;
                                        $truncatedLine =~ s/[\s]+${literalArr[$i]}[\s]+/ /g;
                                        next;                                        
                                    }
                                }
                                else{ # No Match with Unit Literal
                                    next;
                                }
                            }
                        }

                        if ( $deleteFlag == 0){
                            #### Check if truncared Line only has 0 terminator.... It is already unsatisfiable ######
                            if( $truncatedLine eq " 0" ){ # Only One..
                                print "Unsatisfiable! : All Literals are removed.. = $line -> $truncatedLine\n";
								for my $i (0 .. $#literalArr-1){
									print "$varHash_reverse{abs($literalArr[$i])}\n";
								}

                                exit(0);
                            }

                            print $in "$truncatedLine\n";  
                        }
                        else{
                            next;
                        }
                    }
                }
            }
            close ($in);
            close ($out);

            ################ Removing Unit Variables from varHash ##############
            foreach my $key (keys %varHash){
                if(exists($unitLiteral{$varHash{$key}})){        
                    if (exists($varHash{$key})){
                        delete $varHash{$key};
                    }
                    else{
                        print "a $key is not in the hash table\n";
                        exit(-1);
                    }
                    ############# delete element in array #############
                    $varIndex--;
                }
            }
            ###################################################################
        }
    }
}
############# BCP End ################
#
print "a        #Removed Clauses = $numUnitClausesRemoved\n";

##################### Calculation for Variable number has been moved to the end of the file.
$numVarHash = keys %varHash;
$numVarHash -= 1;
$numVar = $numVarHash;

print "a        #Remain Variables = $numVar\n";

###################### Counting New Clauses and Literals #####################
$infile  = "$outdir/$seedName".".cnf.tmp";   ########### select 

open (my $in, "$infile");

### Literal/Clause Count ###
my %literals = ();
my @literalArr = ();
my $numLiterals = 0;
$numClauses = 0;

my $finalClauses_CFC = 0;   #1
my $finalClauses_EUV = 0;   #2
my $finalClauses_ES = 0;    #3
my $finalClauses_MS = 0;    #4
my $finalClauses_WS = 0;    #5
my $finalClauses_GV = 0;    #6
my $finalClauses_MAR = 0;   #7
my $finalClauses_EOL = 0;   #8
my $finalClauses_VR = 0;    #9
my $finalClauses_Unit = 0;  #10

my $finalClauses_PRL = 0;   #11
my $finalClauses_SHR = 0;   #12

$infileStatus = -1;
my $EUVStatus = -1;  # 1 = EUV-NoAdj, 2 = EUV-InnerAdj, 3 = EUV-OuterAdj, 4 = EUV-SS

my $finalClauses_EUV_SS = 0;
my $finalClauses_EUV_NoAdj = 0;
my $finalClauses_EUV_OuterAdj = 0;
my $finalClauses_EUV_InnerAdj = 0;

while (<$in>) {
    my $line = $_;
    chomp($line);
    @literalArr = ();

    # File Status Setting 
    if ($line =~ /^c\s*(\d+).\s/) {
       $infileStatus = $1; 
       next;
    }
    elsif ($line =~/^c\s*EUV-NoAdj/){
       $EUVStatus = 1;
       next;
    }
    elsif ($line =~/^c\s*EUV-InnerAdj/){
       $EUVStatus = 2;
       next;
    }
    elsif ($line =~/^c\s*EUV-OuterAdj/){
       $EUVStatus = 3;
       next;
    }
    elsif ($line =~/^c\s*EUV-SS/){
       $EUVStatus = 4;
       next;
    }
    elsif ($line =~ /^p/){
        next;
    }
    elsif ($line =~ /^c/){  ### Other Comment line for Debugging
        next;
    }
    else{
        if ($line =~ /[\s\t]+0$/) {
            $line =~ s/^[\s]+//g;
            @literalArr = split /[\s\t]+/, $line;
            $numLiterals += $#literalArr;
            $numClauses++;

            if ($infileStatus == 1){
                $finalClauses_CFC++;              
            }
            elsif ($infileStatus == 2){
                $finalClauses_EUV++;
                if ($EUVStatus == 1){
                    $finalClauses_EUV_NoAdj++;
                }
                elsif ($EUVStatus == 2){
                    $finalClauses_EUV_InnerAdj++;
                }
                elsif ($EUVStatus == 3){
                    $finalClauses_EUV_OuterAdj++;
                }
                elsif ($EUVStatus == 4){
                    $finalClauses_EUV_SS++;
                }
                else{
                    print "ERROR - Abnormal EUV Status...\n";
                    exit(-1);
                }
            }
            elsif ($infileStatus == 3){
                $finalClauses_ES++;    
            }
            elsif ($infileStatus == 4){
                $finalClauses_MS++;    
            }
            elsif ($infileStatus == 5){
                $finalClauses_WS++;    
            }
            elsif ($infileStatus == 6){
                $finalClauses_GV++;    
            }
            elsif ($infileStatus == 7){
                $finalClauses_MAR++;    
            }
            elsif ($infileStatus == 8){
                $finalClauses_EOL++;    
            }
            elsif ($infileStatus == 9){
                $finalClauses_VR++;    
            }
            elsif ($infileStatus == 11){
                $finalClauses_PRL++;
            }
            elsif ($infileStatus == 12){
                $finalClauses_SHR++;
            }
            elsif ($infileStatus == 10){
                $finalClauses_Unit++;    
            }

        }
    }
}
close ($in);

my $finalTotalClauses = $finalClauses_CFC + $finalClauses_EUV + $finalClauses_ES + $finalClauses_MS + $finalClauses_WS + $finalClauses_GV + $finalClauses_MAR + $finalClauses_EOL + $finalClauses_VR +
$finalClauses_Unit + $finalClauses_PRL + $finalClauses_SHR;

###### Variable File Generation
$outfile = "$outdir/$seedName".".variables";
open (my $out, '>', $outfile);

print "a     Variable-Index Mapping Table Generation.\n";
print "a     Variable Map File: $outfile\n";

print $out "\#\# Variable-index information of $seedName\.cnf file.\n\n";
print $out "Index    Variable_Name\n";

my $newVarIndex = 1;
my %newHash = ""; 

if ( $BCPEnable == 1) {
    foreach my $key (keys %varHash){
        if($key eq "NULL"){
            next;
        }
        $newHash{$varHash{$key}} = $newVarIndex;
        print $out "$newVarIndex		$key\n";
        $newVarIndex++;
    }

    print "$numTrueUnit\n";
    foreach my $key (keys %TrueUnitClause){
	if($key eq "NULL"){
            next;
        }	
 	print $out "$TrueUnitClause{$key}		$key\n";
    }
}
else{
    foreach my $key (keys %varHash){
        print $out "$varHash{$key}            $key\n";
    }
}

close ($out);


##############################################################################
#### Output File Generation #####
$outfile = "$outdir/$seedName".".cnf";

open (my $in, "$infile");
open (my $out, '>', $outfile);

print $out "c SAT Formulation for SAT Solver\n";
print $out "c   Authors:     ilgweon Kang, Dong Won Park, Daeyeal Lee, Chung-Kuan Cheng\n";
print $out "c   Layout File: $workdir/pinLayouts/$seedName.pinLayout\n";
print $out "c   ILP File:    $workdir/inputsILP/$seedName.lp\n";
print $out "c   DO NOT DISTRIBUTE IN ANY PURPOSE!\n"; 
print $out "c\n"; 
print $out "c   The Total #Variables(For Original Encoding) = $numVar($numVarNet)\n";
print $out "c   The Total #Literals                         = $numLiterals\n";
print $out "c   The Total #Clauses                          = $numClauses\n";
print $out "c   The Total #ILPconstraints                   = $numConstraints\n";
print $out "c\n"; 
print $out "p cnf $numVar $numClauses\n"; 
print $out "c\n"; 
print $out "c\n"; 

while (<$in>) {
    my $line = $_;
    chomp($line);

############## Exchange ##############
    if( $BCPEnable == 1){
        @literalArr = ();

        if ($line =~ /^c/){
            print $out "$line\n";
        }
        elsif ($line =~ /^p/){
            print $out "$line\n";
        }
        else{
            if ($line =~ /[\s\t]+0$/) {
                $line =~ s/^[\s]+//g;
                @literalArr = split /[\s\t]+/, $line;
                my $tmp_val = "";

                if ($#literalArr == 1){
                    print "There are some still unit clauses... : $line\n";
                    #exit(-1);
                }

                for my $i(0 .. $#literalArr-1){
                    if($literalArr[$i] ne ""){
                        $tmp_val = $literalArr[$i];
                        $tmp_val =~ s/-//g;
                        if( exists($newHash{$tmp_val})){
                            $literalArr[$i] =~ s/[0-9]+$/$newHash{$tmp_val}/g;
                        }
                        else{
                            print "There is no variable index key($tmp_val) in new Hash Table : $line\n";
                            exit(-1);
                        }   
                        print $out $literalArr[$i]." ";
                    }
                }
                print $out "0\n";
            }
        }
    }
    else{
        print $out "$line\n";
    }
}

close ($in);
close ($out);
###########################################################################


print "a   SAT Formulation File Complete!!\n";
print "a     The Total #Variables                       = $numVar\n";
print "a     The Total #Literals                        = $numLiterals\n";
print "a     The Total #Clauses                         = $numClauses\n";
print "a     The Total #ILPconstraints                  = $numConstraints\n\n";

print "a     The Original #Clauses_CFC                     = $numClauses_CFC\n";
print "a     The Original #Clauses_CFC_T(EO-$encodeEnable)             = $numClauses_CFC_T\n";
print "a     The Original #Clauses_CFC_S(EO)               = $numClauses_CFC_S\n";
print "a     The Original #Clauses_CFC_NoST                = $numClauses_CFC_NoSS\n";
print "a     The Original #Clauses_CFC_NoST_Pin            = $numClauses_CFC_NoSS_Pin\n\n";


print "a     The Original #Clauses_EUV                     = $numClauses_EUV\n";
print "a     The Original #Clauses_EUV_NoAdj(AMON-$encodeEnable)       = $numClauses_EUV_NoAdj\n";
print "a     The Original #Clauses_EUV_InnerAdj(AMON-$encodeEnable)    = $numClauses_EUV_InnerAdj\n";
print "a     The Original #Clauses_EUV_OuterAdj(AMON-$encodeEnable)    = $numClauses_EUV_OuterAdj\n";
print "a     The Original #Clauses_EUV_SS                  = $numClauses_EUV_SS\n\n";


print "a     The Original #Clauses_MS (EO-$encodeEnable)               = $numClauses_MS\n\n";

print "a     The Original #Clauses_GV                      = $numClauses_GV\n\n";

print "a     The Final #Clauses_CFC                        = $finalClauses_CFC\n";
print "a     The Final #Clauses_EUV                        = $finalClauses_EUV\n";
print "a     The Final #Clauses_ES                         = $finalClauses_ES\n";
print "a     The Final #Clauses_MS                         = $finalClauses_MS\n";
print "a     The Final #Clauses_WS                         = $finalClauses_WS\n";
print "a     The Final #Clauses_GV                         = $finalClauses_GV\n";
print "a     The Final #Clauses_MAR                        = $finalClauses_MAR\n";
print "a     The Final #Clauses_EOL                        = $finalClauses_EOL\n";
print "a     The Final #Clauses_VR                         = $finalClauses_VR\n";
print "a     The Final #Clauses_PRL                        = $finalClauses_PRL\n";
print "a     The Final #Clauses_SHR                        = $finalClauses_SHR\n\n";

print "a     The Final #Clauses                            = $finalTotalClauses\n\n";

print "a     The Final #Clauses_EUV_NoAdj                  = $finalClauses_EUV_NoAdj\n";
print "a     The Final #Clauses_EUV_InnerAdj               = $finalClauses_EUV_InnerAdj\n";
print "a     The Final #Clauses_EUV_OuterAdj               = $finalClauses_EUV_OuterAdj\n";
print "a     The Final #Clauses_EUV_SS                     = $finalClauses_EUV_SS\n\n";


print "a   CNF FILE: $outfile\n\n";

exec "rm -rf $infile $bcpfile1";
