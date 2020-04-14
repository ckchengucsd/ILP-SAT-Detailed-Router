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
my $outdir      = "$workdir/solutionsILP";
my $infile      = "";

if ($ARGC != 1) {
    print "\n*** Error:: Wrong CMD";
    print "\n   [USAGE]: ./PL_FILE [inputfile_result]\n\n";
    exit(-1);
} else {
    $infile             = $ARGV[0];
}

if (!-e "./$infile") {
    print "\n*** Error:: FILE DOES NOT EXIST..\n";
    print "***         $workdir/$infile\n\n";
    exit(-1);
}

### Output Directory Creation, please see the following reference:
system "mkdir -p $outdir";

my $infileStatus = "init";

## Instance Info
my @inst = ();
my %h_inst = ();
my $idx_inst = 0;
## Metal/VIA Info
my @metal = ();
my @via = ();
my @final_metal = ();
my @final_via = ();
my @obs_metal = ();
my @obs_via = ();
my @m_metal = ();
my @m_obs_metal = ();
my %h_metal = ();
my %h_obs_metal = ();
my %h_m_metal = ();
my %h_m_obs_metal = ();
my $idx_m_metal = 0;
my $idx_m_obs_metal = 0;
## Wire
my @wire = ();
my @via_wire = ();
my @obs_wire = ();
my @obs_via_wire = ();
my %h_wire = ();
my %h_obs_wire = ();
my %h_via_wire = ();
## Internal Pin Info
my @pin = ();
my @obs_pin = ();
my %h_pin = ();
my @pin_layout = ();
## Net
my @net = ();
my %h_net = ();
## Cost
my $cost = 0;
my $cost_placement = 0;
my $cost_ml = 0;
my $cost_wl = 0;

my $isFirst = 1;
my $subIndex = 0;

my $out;
my $outfile = "";
### Read Inputfile and Build Data Structure
open (my $in, "./$infile");
while (<$in>) {
    my $line = $_;
    chomp($line);

	if ($line =~ /^header/){
		if($isFirst == 1){
			$isFirst = 0;
			next;
		}
		else{
			$outfile     = "$outdir/".(split /\./, (split /\//, $infile)[$#_])[0]."_$subIndex\_C_$cost\_$cost_ml\_$cost_wl.conv";
			open ($out,'>', $outfile);
			printResult();
			close($out);
			@inst = ();
			%h_inst = ();
			$idx_inst = 0;
			@metal = ();
			@via = ();
			@pin = ();
			%h_pin = ();
			@pin_layout = ();
			@wire = ();
			@via_wire = ();
			%h_wire = ();
			%h_via_wire = ();
			$cost = 0;
			$cost_placement = 0;
			$cost_ml = 0;
			$cost_wl = 0;
			$subIndex++;
		}
	}

    ### COST
    if ($line =~ /ANS".*value="(\S+)"/) {
		$cost = $1;
    } 
    ### Metal
    if ($line =~ /name="M\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)".*value="(\S+)"/) {
		my $fromM = $1;
		my $toM = $4;
		my $fromR = $2;
		my $toR = $5;
		my $fromC = $3;
		my $toC = $6;
		$line = int($7 + 0.5);

		if($line == 1){
			# Metal Line
			if($fromM == $toM){
				#@metal = [numLayer, fromRow, fromCol, toRow, toCol];
				push(@metal, [($fromM, $fromR, $fromC, $toR, $toC)]);
				if($fromM != 1){
					$cost_ml++;
				}
			}
			else{
				#@via = [fromMetalLayer, toMetalLayer, Row, Col]
				push(@via, [($fromM, $toM, $fromR, $fromC)]);
				$cost_ml = $cost_ml + 4;
#print "VIA $fromM $toM $fromR $fromC\n";
			}
		}
    } 
    ### Wire
    if ($line =~ /name="N(\S+)_C(\S+)_E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)".*value="(\S+)"/) {
		my $fromM = $3;
		my $toM = $6;
		my $fromR = $4;
		my $toR = $7;
		my $fromC = $5;
		my $toC = $8;
		$line = int($9 + 0.5);

		if($line == 1){
			if(!exists($h_wire{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC})){
				#print "VIA_WIRE $fromM $toM $fromR $fromC $toR $toC\n";
				# Metal Line
				if($fromM == $toM){
					#@metal = [numLayer, fromRow, fromCol, toRow, toCol];
					push(@wire, [($fromM, $fromR, $fromC, $toR, $toC)]);
					if($fromM != 1){
						$cost_wl++;
					}
				}
				else{
					#@via = [fromMetalLayer, toMetalLayer, Row, Col]
					push(@via_wire, [($fromM, $toM, $fromR, $fromC)]);
					#print "VIA $fromM $toM $fromR $fromC\n";
					$cost_wl = $cost_wl + 4;
				}
				$h_wire{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC} = 1;
			}
		}
    } 
	### Net
	if ($line =~ /name="N(\S+)_E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)".*value="(\S+)"/) {
		my $netID = $1;
		my $fromM = $2;
		my $toM = $5;
		my $fromR = $3;
		my $toR = $6;
		my $fromC = $4;
		my $toC = $7;
		$line = int($8 + 0.5);
		if($netID =~ /_C/){
			next;
		}

		if($line == 1){
			if(!exists($h_net{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC})){
				#@net = [numLayer, fromRow, fromCol, toRow, toCol];
				push(@net, [($fromM, $fromR, $fromC, $toR, $toC)]);
				$h_net{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC} = $netID;
				$h_net{$fromM."_".$toM."_".$toR."_".$fromC."_".$fromR."_".$toC} = $netID;
				$h_net{$fromM."_".$toM."_".$fromR."_".$toC."_".$toR."_".$fromC} = $netID;
				$h_net{$toM."_".$fromM."_".$fromR."_".$fromC."_".$toR."_".$toC} = $netID;
			}
		}
	} 
    ### Pin
	if ($line =~ /name="N(\d+)_E\(m(\d+)r(\d+)c(\d+)\)\(pinSON\)".*value="(\S+)"/) {
		my $net = $1;
		my $row = $3;
		my $col = $4;
		$line = int($5 + 0.5);

		if($line == 1){
			#@obs_pin = [net, row, col]
			push(@obs_pin, [($net, $row, $col)]);
		}
	}
	if ($line =~ /name="N(\d+)_E\(pinSON\)\(m(\d+)r(\d+)c(\d+)\)".*value="(\S+)"/) {
		my $net = $1;
		my $row = $3;
		my $col = $4;
		$line = int($5 + 0.5);

		if($line == 1){
			#@obs_pin = [net, row, col]
			push(@obs_pin, [($net, $row, $col)]);
		}
	}
}
close ($in);

$outfile     = "$outdir/".(split /\./, (split /\//, $infile)[$#_])[0]."_$subIndex\_C_$cost\_$cost_ml\_$cost_wl.conv";
open ($out,'>', $outfile);
mergeVertices();
printResult();
close($out);

sub mergeVertices{
	my $idx_obs_metal = 0;
	my $idx_metal = 0;
	for my $i(0 .. (scalar @metal) -1){
		if(!exists($h_net{$metal[$i][0]."_".$metal[$i][0]."_".$metal[$i][1]."_".$metal[$i][2]."_".$metal[$i][3]."_".$metal[$i][4]})){
			push(@obs_metal, [($metal[$i][0], $metal[$i][1], $metal[$i][2], $metal[$i][3], $metal[$i][4])]);
			$h_obs_metal{$metal[$i][0]."_".$metal[$i][0]."_".$metal[$i][1]."_".$metal[$i][2]."_".$metal[$i][3]."_".$metal[$i][4]} = $idx_obs_metal;
			$idx_obs_metal++;	
		}
		else{
			push(@final_metal, [($metal[$i][0], $metal[$i][1], $metal[$i][2], $metal[$i][3], $metal[$i][4])]);
			$h_metal{$metal[$i][0]."_".$metal[$i][0]."_".$metal[$i][1]."_".$metal[$i][2]."_".$metal[$i][3]."_".$metal[$i][4]} = $idx_metal;
			$idx_metal++;
		}
	}
	for my $i(0 .. (scalar @via) -1){
		if(!exists($h_net{$via[$i][0]."_".$via[$i][1]."_".$via[$i][2]."_".$via[$i][3]."_".$via[$i][2]."_".$via[$i][3]})){
			push(@obs_via, [($via[$i][0], $via[$i][1], $via[$i][2], $via[$i][3])]);
		}
		else{
			push(@final_via, [($via[$i][0], $via[$i][1], $via[$i][2], $via[$i][3])]);
		}
	}
	my $prev_cnt = 0;
	my $cur_cnt = 0;
	$prev_cnt = keys %h_metal;
	$cur_cnt = keys %h_metal;
	while($cur_cnt > 0){
		if($prev_cnt == $cur_cnt){
			foreach my $key(keys %h_metal){
				my $idx = $h_metal{$key};
				push(@m_metal, [($final_metal[$idx][0], $final_metal[$idx][1], $final_metal[$idx][2], $final_metal[$idx][3], $final_metal[$idx][4])]);
				$h_m_metal{ $final_metal[$idx][0]."_".$final_metal[$idx][1]."_".$final_metal[$idx][2]."_".$final_metal[$idx][3]."_".$final_metal[$idx][4]} = $idx_m_metal;
				$idx_m_metal++;
				delete $h_metal{$key};
#				print "NEW METAL $final_metal[$idx][0]: $final_metal[$idx][1] -> $final_metal[$idx][3], $final_metal[$idx][2] -> $final_metal[$idx][4]\n";
				last;
			}
		}
		$prev_cnt = keys %h_metal;
		foreach my $key(keys %h_metal){
			my $idx = $h_metal{$key};
			for(my $i=0; $i<=$#m_metal; $i++){
				if($m_metal[$i][0] eq $final_metal[$idx][0]){
					# Vertical
					if($final_metal[$idx][1] != $final_metal[$idx][3] && $m_metal[$i][1] != $m_metal[$i][3] && $m_metal[$i][2] == $m_metal[$i][4]){
						if($m_metal[$i][1] == $final_metal[$idx][3] && $m_metal[$i][2] == $final_metal[$idx][2]){
							$m_metal[$i][1] = $final_metal[$idx][1];
							delete $h_metal{$key};
#print "EXT METAL $final_metal[$idx][0]: $final_metal[$idx][1] -> $final_metal[$idx][3], $final_metal[$idx][2] -> $final_metal[$idx][4]";
#print " => $m_metal[$i][1] -> $m_metal[$i][3], $m_metal[$i][2] -> $m_metal[$i][4]\n";
						}
						elsif($m_metal[$i][3] == $final_metal[$idx][1] && $m_metal[$i][2] == $final_metal[$idx][2] && $m_metal[$i][2] == $m_metal[$i][4]){
							$m_metal[$i][3] = $final_metal[$idx][3];
							delete $h_metal{$key};
#print "EXT METAL $final_metal[$idx][0]: $final_metal[$idx][1] -> $final_metal[$idx][3], $final_metal[$idx][2] -> $final_metal[$idx][4]";
#print " => $m_metal[$i][1] -> $m_metal[$i][3], $m_metal[$i][2] -> $m_metal[$i][4]\n";
						}
					}
					# Horizontal
					elsif($final_metal[$idx][2] != $final_metal[$idx][4] && $m_metal[$i][2] != $m_metal[$i][4] && $m_metal[$i][1] == $m_metal[$i][3]){
						if($m_metal[$i][2] == $final_metal[$idx][4] && $m_metal[$i][1] == $final_metal[$idx][1]){
							$m_metal[$i][2] = $final_metal[$idx][2];
							delete $h_metal{$key};
#print "EXT METAL $final_metal[$idx][0]: $final_metal[$idx][1] -> $final_metal[$idx][3], $final_metal[$idx][2] -> $final_metal[$idx][4]";
#print " => $m_metal[$i][1] -> $m_metal[$i][3], $m_metal[$i][2] -> $m_metal[$i][4]\n";
						}
						elsif($m_metal[$i][4] == $final_metal[$idx][2] && $m_metal[$i][1] == $final_metal[$idx][1] && $m_metal[$i][1] == $m_metal[$i][3]){
							$m_metal[$i][4] = $final_metal[$idx][4];
							delete $h_metal{$key};
#print "EXT METAL $final_metal[$idx][0]: $final_metal[$idx][1] -> $final_metal[$idx][3], $final_metal[$idx][2] -> $final_metal[$idx][4]";
#print " => $m_metal[$i][1] -> $m_metal[$i][3], $m_metal[$i][2] -> $m_metal[$i][4]\n";
						}
					}
				}
			}
		}
		$cur_cnt = keys %h_metal;
	}
	$prev_cnt = keys %h_obs_metal;
	$cur_cnt = keys %h_obs_metal;
	while($cur_cnt > 0){
		if($prev_cnt == $cur_cnt){
			foreach my $key(keys %h_obs_metal){
				my $idx = $h_obs_metal{$key};
				push(@m_obs_metal, [($obs_metal[$idx][0], $obs_metal[$idx][1], $obs_metal[$idx][2], $obs_metal[$idx][3], $obs_metal[$idx][4])]);
				$h_m_obs_metal{ $obs_metal[$idx][0]."_".$obs_metal[$idx][1]."_".$obs_metal[$idx][2]."_".$obs_metal[$idx][3]."_".$obs_metal[$idx][4]} = $idx_m_obs_metal;
				$idx_m_obs_metal++;
				delete $h_obs_metal{$key};
#				print "NEW METAL $obs_metal[$idx][0]: $obs_metal[$idx][1] -> $obs_metal[$idx][3], $obs_metal[$idx][2] -> $obs_metal[$idx][4]\n";
				last;
			}
		}
		$prev_cnt = keys %h_obs_metal;
		foreach my $key(keys %h_obs_metal){
			my $idx = $h_obs_metal{$key};
			for(my $i=0; $i<=$#m_obs_metal; $i++){
				if($m_obs_metal[$i][0] eq $obs_metal[$idx][0]){
					# Vertical
					if($obs_metal[$idx][1] != $obs_metal[$idx][3] && $m_obs_metal[$i][1] != $m_obs_metal[$i][3] && $m_obs_metal[$i][2] == $m_obs_metal[$i][4]){
						if($m_obs_metal[$i][1] == $obs_metal[$idx][3] && $m_obs_metal[$i][2] == $obs_metal[$idx][2]){
							$m_obs_metal[$i][1] = $obs_metal[$idx][1];
							delete $h_obs_metal{$key};
#print "EXT METAL $obs_metal[$idx][0]: $obs_metal[$idx][1] -> $obs_metal[$idx][3], $obs_metal[$idx][2] -> $obs_metal[$idx][4]";
#print " => $m_obs_metal[$i][1] -> $m_obs_metal[$i][3], $m_obs_metal[$i][2] -> $m_obs_metal[$i][4]\n";
						}
						elsif($m_obs_metal[$i][3] == $obs_metal[$idx][1] && $m_obs_metal[$i][2] == $obs_metal[$idx][2] && $m_obs_metal[$i][2] == $m_obs_metal[$i][4]){
							$m_obs_metal[$i][3] = $obs_metal[$idx][3];
							delete $h_obs_metal{$key};
#print "EXT METAL $obs_metal[$idx][0]: $obs_metal[$idx][1] -> $obs_metal[$idx][3], $obs_metal[$idx][2] -> $obs_metal[$idx][4]";
#print " => $m_obs_metal[$i][1] -> $m_obs_metal[$i][3], $m_obs_metal[$i][2] -> $m_obs_metal[$i][4]\n";
						}
					}
					# Horizontal
					elsif($obs_metal[$idx][2] != $obs_metal[$idx][4] && $m_obs_metal[$i][2] != $m_obs_metal[$i][4] && $m_obs_metal[$i][1] == $m_obs_metal[$i][3]){
						if($m_obs_metal[$i][2] == $obs_metal[$idx][4] && $m_obs_metal[$i][1] == $obs_metal[$idx][1]){
							$m_obs_metal[$i][2] = $obs_metal[$idx][2];
							delete $h_obs_metal{$key};
#print "EXT METAL $obs_metal[$idx][0]: $obs_metal[$idx][1] -> $obs_metal[$idx][3], $obs_metal[$idx][2] -> $obs_metal[$idx][4]";
#print " => $m_obs_metal[$i][1] -> $m_obs_metal[$i][3], $m_obs_metal[$i][2] -> $m_obs_metal[$i][4]\n";
						}
						elsif($m_obs_metal[$i][4] == $obs_metal[$idx][2] && $m_obs_metal[$i][1] == $obs_metal[$idx][1] && $m_obs_metal[$i][1] == $m_obs_metal[$i][3]){
							$m_obs_metal[$i][4] = $obs_metal[$idx][4];
							delete $h_obs_metal{$key};
#print "EXT METAL $obs_metal[$idx][0]: $obs_metal[$idx][1] -> $obs_metal[$idx][3], $obs_metal[$idx][2] -> $obs_metal[$idx][4]";
#print " => $m_obs_metal[$i][1] -> $m_obs_metal[$i][3], $m_obs_metal[$i][2] -> $m_obs_metal[$i][4]\n";
						}
					}
				}
			}
		}
		$cur_cnt = keys %h_obs_metal;
	}
}
sub printResult{
	print $out "COST $cost_ml $cost_wl\r\n";
	for my $i(0 .. (scalar @pin_layout) -1){
		print $out "PIN_LAYOUT $pin_layout[$i][0] $pin_layout[$i][1] $pin_layout[$i][2] $pin_layout[$i][3] $pin_layout[$i][4]\r\n";
	}
	for my $i(0 .. (scalar @m_obs_metal) -1){
		#print "Metal Layer => $metal[$i][0] fromRow=$metal[$i][1] fromCol=$metal[$i][2] toRow=$metal[$i][3] toCol=$metal[$i][4]\n";
		print $out "OBS_METAL $m_obs_metal[$i][0] $m_obs_metal[$i][1] $m_obs_metal[$i][2] $m_obs_metal[$i][3] $m_obs_metal[$i][4]\r\n";
	}
	for my $i(0 .. (scalar @obs_via) -1){
		#print "VIA : FromMetal => $via[$i][0] ToMetal=$via[$i][1] Row=$via[$i][2] Col=$via[$i][3]\n";
		print $out "OBS_VIA $obs_via[$i][0] $obs_via[$i][1] $obs_via[$i][2] $obs_via[$i][3]\r\n";
	}
	for my $i(0 .. (scalar @obs_pin) -1){
		#print "EXTERNAL PIN : NetID => $obs_pin[$i][0] Row=$obs_pin[$i][1] Col=$obs_pin[$i][2]\n";
		print $out "OBS_PIN $obs_pin[$i][0] $obs_pin[$i][1] $obs_pin[$i][2]\r\n";
	}
	for my $i(0 .. (scalar @pin) -1){
		#print "Internal PIN : Name => $pin[$i][0] Row=$pin[$i][1] Col=$pin[$i][2]\n";
		print $out "PIN $pin[$i][0] $pin[$i][1] $pin[$i][2]\r\n";
	}
	for my $i(0 .. (scalar @m_metal) -1){
		#print "Metal Layer => $m_metal[$i][0] fromRow=$m_metal[$i][1] fromCol=$m_metal[$i][2] toRow=$m_metal[$i][3] toCol=$m_metal[$i][4]\n";
		if($m_metal[$i][0] == 1){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @m_metal) -1){
		#print "Metal Layer => $m_metal[$i][0] fromRow=$m_metal[$i][1] fromCol=$m_metal[$i][2] toRow=$m_metal[$i][3] toCol=$m_metal[$i][4]\n";
		if($m_metal[$i][0] == 2){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @m_metal) -1){
		#print "Metal Layer => $m_metal[$i][0] fromRow=$m_metal[$i][1] fromCol=$m_metal[$i][2] toRow=$m_metal[$i][3] toCol=$m_metal[$i][4]\n";
		if($m_metal[$i][0] == 3){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @m_metal) -1){
		#print "Metal Layer => $m_metal[$i][0] fromRow=$m_metal[$i][1] fromCol=$m_metal[$i][2] toRow=$m_metal[$i][3] toCol=$m_metal[$i][4]\n";
		if($m_metal[$i][0] == 4){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
		#print "Metal Layer => $wire[$i][0] fromRow=$wire[$i][1] fromCol=$wire[$i][2] toRow=$wire[$i][3] toCol=$wire[$i][4]\n";
		if($wire[$i][0] == 1){
			if($wire[$i][1]>$wire[$i][3]){
				print $out "WIRE $wire[$i][0] $wire[$i][3] $wire[$i][2] $wire[$i][1] $wire[$i][4]\r\n";
			}
			elsif($wire[$i][2]>$wire[$i][4]){
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][4] $wire[$i][3] $wire[$i][2]\r\n";
			}
			else{
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][2] $wire[$i][3] $wire[$i][4]\r\n";
			}
		}
	}
	for my $i(0 .. (scalar @via_wire) -1){
		#print "VIA_WIRE : FromMetal => $via_wire[$i][0] ToMetal=$via_wire[$i][1] Row=$via_wire[$i][2] Col=$via_wire[$i][3]\n";
		if($via_wire[$i][0] == 1 && $via_wire[$i][1] == 2){
			print $out "VIA_WIRE $via_wire[$i][0] $via_wire[$i][1] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
		if($via_wire[$i][0] == 2 && $via_wire[$i][1] == 1){
			print $out "VIA_WIRE $via_wire[$i][1] $via_wire[$i][0] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
		#print "Metal Layer => $wire[$i][0] fromRow=$wire[$i][1] fromCol=$wire[$i][2] toRow=$wire[$i][3] toCol=$wire[$i][4]\n";
		if($wire[$i][0] == 2){
			if($wire[$i][1]>$wire[$i][3]){
				print $out "WIRE $wire[$i][0] $wire[$i][3] $wire[$i][2] $wire[$i][1] $wire[$i][4]\r\n";
			}
			elsif($wire[$i][2]>$wire[$i][4]){
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][4] $wire[$i][3] $wire[$i][2]\r\n";
			}
			else{
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][2] $wire[$i][3] $wire[$i][4]\r\n";
			}
		}
	}
	for my $i(0 .. (scalar @via_wire) -1){
		#print "VIA_WIRE : FromMetal => $via_wire[$i][0] ToMetal=$via_wire[$i][1] Row=$via_wire[$i][2] Col=$via_wire[$i][3]\n";
		if($via_wire[$i][0] == 2 && $via_wire[$i][1] == 3){
			print $out "VIA_WIRE $via_wire[$i][0] $via_wire[$i][1] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
		if($via_wire[$i][0] == 3 && $via_wire[$i][1] == 2){
			print $out "VIA_WIRE $via_wire[$i][1] $via_wire[$i][0] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
		#print "Metal Layer => $wire[$i][0] fromRow=$wire[$i][1] fromCol=$wire[$i][2] toRow=$wire[$i][3] toCol=$wire[$i][4]\n";
		if($wire[$i][0] == 3){
			if($wire[$i][1]>$wire[$i][3]){
				print $out "WIRE $wire[$i][0] $wire[$i][3] $wire[$i][2] $wire[$i][1] $wire[$i][4]\r\n";
			}
			elsif($wire[$i][2]>$wire[$i][4]){
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][4] $wire[$i][3] $wire[$i][2]\r\n";
			}
			else{
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][2] $wire[$i][3] $wire[$i][4]\r\n";
			}
		}
	}
	for my $i(0 .. (scalar @via_wire) -1){
		#print "VIA_WIRE : FromMetal => $via_wire[$i][0] ToMetal=$via_wire[$i][1] Row=$via_wire[$i][2] Col=$via_wire[$i][3]\n";
		if($via_wire[$i][0] == 3 && $via_wire[$i][1] == 4){
			print $out "VIA_WIRE $via_wire[$i][0] $via_wire[$i][1] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
		if($via_wire[$i][0] == 4 && $via_wire[$i][1] == 3){
			print $out "VIA_WIRE $via_wire[$i][1] $via_wire[$i][0] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
		#print "Metal Layer => $wire[$i][0] fromRow=$wire[$i][1] fromCol=$wire[$i][2] toRow=$wire[$i][3] toCol=$wire[$i][4]\n";
		if($wire[$i][0] == 4){
			if($wire[$i][1]>$wire[$i][3]){
				print $out "WIRE $wire[$i][0] $wire[$i][3] $wire[$i][2] $wire[$i][1] $wire[$i][4]\r\n";
			}
			elsif($wire[$i][2]>$wire[$i][4]){
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][4] $wire[$i][3] $wire[$i][2]\r\n";
			}
			else{
				print $out "WIRE $wire[$i][0] $wire[$i][1] $wire[$i][2] $wire[$i][3] $wire[$i][4]\r\n";
			}
		}
	}
	for my $i(0 .. (scalar @final_via) -1){
		#print "VIA : FromMetal => $final_via[$i][0] ToMetal=$final_via[$i][1] Row=$final_via[$i][2] Col=$final_via[$i][3]\n";
		if($final_via[$i][0] == 3 && $final_via[$i][1] == 4){
			my $netID = $h_net{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]};
			print $out "VIA $final_via[$i][0] $final_via[$i][1] $final_via[$i][2] $final_via[$i][3] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @final_via) -1){
		#print "VIA : FromMetal => $final_via[$i][0] ToMetal=$final_via[$i][1] Row=$final_via[$i][2] Col=$final_via[$i][3]\n";
		if($final_via[$i][0] == 2 && $final_via[$i][1] == 3){
			my $netID = $h_net{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]};
			print $out "VIA $final_via[$i][0] $final_via[$i][1] $final_via[$i][2] $final_via[$i][3] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @final_via) -1){
		#print "VIA : FromMetal => $final_via[$i][0] ToMetal=$final_via[$i][1] Row=$final_via[$i][2] Col=$final_via[$i][3]\n";
		if($final_via[$i][0] == 1 && $final_via[$i][1] == 2){
			my $netID = $h_net{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]};
			print $out "VIA $final_via[$i][0] $final_via[$i][1] $final_via[$i][2] $final_via[$i][3] $netID\r\n";
		}
	}
	print "Converting Result Completed!\nOutput : $outfile\n";
}
