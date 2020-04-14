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
my $outdir      = "$workdir/solutionsSAT";
my $indir		= "$workdir/inputsSAT";
my $infile      = "";

if ($ARGC != 1) {
    print "\n*** Error:: Wrong CMD";
    print "\n   [USAGE]: ./PL_FILE [inputfile_result]\n\n";
    exit(-1);
} else {
    $infile             = $ARGV[0];
}

my $infile_var = "$indir/".(split /\./, (split /\//, $infile)[$#_])[0].".variables";
if (!-e "./$infile") {
    print "\n*** Error:: FILE DOES NOT EXIST..\n";
    print "***         $workdir/$infile\n\n";
    exit(-1);
}
if (!-e "$infile_var") {
    print "\n*** Error:: FILE DOES NOT EXIST..\n";
    print "***         $infile_var\n\n";
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
my $cost_placement = 0;
my $cost_ml = 0;
my $cost_wl = 0;

my $isFirst = 1;
my $subIndex = 0;

my $out;
my $outfile = "";

my %h_var = ();
my %h_var_1 = ();
my %h_var_sol = ();
my @var = ();

### Read Variable File
open (my $in, "$infile_var");
while (<$in>) {
    my $line = $_;
    chomp($line);

    if ($line =~ /^(\d+)\s*(\S+)/){
		$h_var{$1} = $2;
	}
    elsif ($line =~ /^-1\s*(\S+)/){
		$h_var_1{$1} = $1;
	}
}
### Read Solution and Build Data Structure
open (my $in, "./$infile");
while (<$in>) {
    my $line = $_;
    chomp($line);

    if ($line =~ /^v (.*)/){
		@var = split /\s+/, $line;
		for(my $i=1; $i<=$#var; $i++){
			if($var[$i] ne "0"){
				if($var[$i] =~ /-(\d+)/){
					$h_var_sol{$h_var{$1}} = 0;
					next;
				}
				else{
					$h_var_sol{$h_var{$var[$i]}} = 1;
					my $r_var = "";
					if(exists($h_var{$var[$i]})){
						$r_var = $h_var{$var[$i]};
					}
					else{
						print "[ERROR] Variable Matching Fail [$var[$i]]\n";
						exit(-1);
					}
					### Metal
					if ($r_var =~ /^M\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)/) {
						my $fromM = $1;
						my $toM = $4;
						my $fromR = $2;
						my $toR = $5;
						my $fromC = $3;
						my $toC = $6;

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
						}
					} 
					### Wire
					if ($r_var =~ /^N(\S+)_C(\S+)_E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)/) {
						my $fromM = $3;
						my $toM = $6;
						my $fromR = $4;
						my $toR = $7;
						my $fromC = $5;
						my $toC = $8;

						if(!exists($h_wire{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC})){
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
								$cost_wl = $cost_wl + 4;
							}
							$h_wire{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC} = 1;
						}
					} 
					### Net
					if ($r_var =~ /^N(\S+)_E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)/) {
						my $netID = $1;
						my $fromM = $2;
						my $toM = $5;
						my $fromR = $3;
						my $toR = $6;
						my $fromC = $4;
						my $toC = $7;
						if($netID =~ /_C/){
							next;
						}

						if(!exists($h_net{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC})){
							#@net = [numLayer, fromRow, fromCol, toRow, toCol];
							push(@net, [($fromM, $fromR, $fromC, $toR, $toC)]);
							$h_net{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC} = $netID;
							$h_net{$fromM."_".$toM."_".$toR."_".$fromC."_".$fromR."_".$toC} = $netID;
							$h_net{$fromM."_".$toM."_".$fromR."_".$toC."_".$toR."_".$fromC} = $netID;
							$h_net{$toM."_".$fromM."_".$fromR."_".$fromC."_".$toR."_".$toC} = $netID;
						}
					} 
					### Pin
					if ($r_var =~ /^M\(.*r(\d+)c(\d+)\)\((pin[0-9_]+)\)/) {
						my $pinName = $3;
						my $row = $1;
						my $col = $2;

						#@pin = [pinName, row, col]
						push(@pin, [($pinName, $row, $col)]);
						$h_pin{$pinName} = 1;
					}
					if ($r_var =~ /^M\((pin[0-9_]+)\)\(.*r(\d+)c(\d+)\)/) {
						my $pinName = $1;
						my $row = $2;
						my $col = $3;

						#@pin = [pinName, row, col]
						push(@pin, [($pinName, $row, $col)]);
						$h_pin{$pinName} = 1;
					}
				}
			}
		}
	}
}
close ($in);

## process fixed 1 variables
foreach my $key(keys %h_var_1){
	my $r_var = $key;
	$h_var_sol{$r_var} = 1;
	### Metal
	if ($r_var =~ /^M\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)/) {
		my $fromM = $1;
		my $toM = $4;
		my $fromR = $2;
		my $toR = $5;
		my $fromC = $3;
		my $toC = $6;

		# Metal Line
		if($fromM == $toM){
			push(@metal, [($fromM, $fromR, $fromC, $toR, $toC)]);
			if($fromM != 1){
				$cost_ml++;
			}
		}
		else{
			push(@via, [($fromM, $toM, $fromR, $fromC)]);
			$cost_ml = $cost_ml + 4;
		}
	} 
	### Wire
	if ($r_var =~ /^N(\S+)_C(\S+)_E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)/) {
		my $fromM = $3;
		my $toM = $6;
		my $fromR = $4;
		my $toR = $7;
		my $fromC = $5;
		my $toC = $8;

		if(!exists($h_wire{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC})){
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
			}
			$h_wire{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC} = 1;
		}
	} 
	### Pin
	if ($r_var =~ /^N(\d+)_E\(m(\d+)r(\d+)c(\d+)\)\((pinSON)\)/) {
		my $net = $1;
		my $row = $3;
		my $col = $4;

		#@pin = [pinName, row, col]
		push(@obs_pin, [($net, $row, $col)]);
	}
	### Net
	if ($r_var =~ /^N(\S+)_E\(m(\d+)r(\d+)c(\d+)\)\(m(\d+)r(\d+)c(\d+)\)/) {
		my $netID = $1;
		my $fromM = $2;
		my $toM = $5;
		my $fromR = $3;
		my $toR = $6;
		my $fromC = $4;
		my $toC = $7;

		if($netID =~ /_C/){
			next;
		}

		if(!exists($h_net{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC})){
			#@net = [numLayer, fromRow, fromCol, toRow, toCol];
			push(@net, [($fromM, $fromR, $fromC, $toR, $toC, $netID)]);
			$h_net{$fromM."_".$toM."_".$fromR."_".$fromC."_".$toR."_".$toC} = $netID;
			$h_net{$fromM."_".$toM."_".$toR."_".$fromC."_".$fromR."_".$toC} = $netID;
			$h_net{$fromM."_".$toM."_".$fromR."_".$toC."_".$toR."_".$fromC} = $netID;
			$h_net{$toM."_".$fromM."_".$fromR."_".$fromC."_".$toR."_".$toC} = $netID;
		}
	} 
}

$outfile     = "$outdir/".(split /\./, (split /\//, $infile)[$#_])[0]."_$subIndex\_C_$cost_ml\_$cost_wl.conv";
open ($out,'>', $outfile);
mergeVertices();
printResult();
close($out);
$outfile     = "$outdir/".(split /\./, (split /\//, $infile)[$#_])[0]."_$subIndex\_C_$cost_ml\_$cost_wl.sol";
open ($out,'>', $outfile);
foreach my $key(keys %h_var_sol){
	print $out "$key $h_var_sol{$key}\n";
}
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
						}
						elsif($m_metal[$i][3] == $final_metal[$idx][1] && $m_metal[$i][2] == $final_metal[$idx][2] && $m_metal[$i][2] == $m_metal[$i][4]){
							$m_metal[$i][3] = $final_metal[$idx][3];
							delete $h_metal{$key};
						}
					}
					# Horizontal
					elsif($final_metal[$idx][2] != $final_metal[$idx][4] && $m_metal[$i][2] != $m_metal[$i][4] && $m_metal[$i][1] == $m_metal[$i][3]){
						if($m_metal[$i][2] == $final_metal[$idx][4] && $m_metal[$i][1] == $final_metal[$idx][1]){
							$m_metal[$i][2] = $final_metal[$idx][2];
							delete $h_metal{$key};
						}
						elsif($m_metal[$i][4] == $final_metal[$idx][2] && $m_metal[$i][1] == $final_metal[$idx][1] && $m_metal[$i][1] == $m_metal[$i][3]){
							$m_metal[$i][4] = $final_metal[$idx][4];
							delete $h_metal{$key};
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
						}
						elsif($m_obs_metal[$i][3] == $obs_metal[$idx][1] && $m_obs_metal[$i][2] == $obs_metal[$idx][2] && $m_obs_metal[$i][2] == $m_obs_metal[$i][4]){
							$m_obs_metal[$i][3] = $obs_metal[$idx][3];
							delete $h_obs_metal{$key};
						}
					}
					# Horizontal
					elsif($obs_metal[$idx][2] != $obs_metal[$idx][4] && $m_obs_metal[$i][2] != $m_obs_metal[$i][4] && $m_obs_metal[$i][1] == $m_obs_metal[$i][3]){
						if($m_obs_metal[$i][2] == $obs_metal[$idx][4] && $m_obs_metal[$i][1] == $obs_metal[$idx][1]){
							$m_obs_metal[$i][2] = $obs_metal[$idx][2];
							delete $h_obs_metal{$key};
						}
						elsif($m_obs_metal[$i][4] == $obs_metal[$idx][2] && $m_obs_metal[$i][1] == $obs_metal[$idx][1] && $m_obs_metal[$i][1] == $m_obs_metal[$i][3]){
							$m_obs_metal[$i][4] = $obs_metal[$idx][4];
							delete $h_obs_metal{$key};
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
		print $out "OBS_METAL $m_obs_metal[$i][0] $m_obs_metal[$i][1] $m_obs_metal[$i][2] $m_obs_metal[$i][3] $m_obs_metal[$i][4]\r\n";
	}
	for my $i(0 .. (scalar @obs_via) -1){
		print $out "OBS_VIA $obs_via[$i][0] $obs_via[$i][1] $obs_via[$i][2] $obs_via[$i][3]\r\n";
	}
	for my $i(0 .. (scalar @obs_pin) -1){
		print $out "OBS_PIN $obs_pin[$i][0] $obs_pin[$i][1] $obs_pin[$i][2]\r\n";
	}
	for my $i(0 .. (scalar @pin) -1){
		print $out "PIN $pin[$i][0] $pin[$i][1] $pin[$i][2]\r\n";
	}
	for my $i(0 .. (scalar @m_metal) -1){
		if($m_metal[$i][0] == 1){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @m_metal) -1){
		if($m_metal[$i][0] == 2){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @m_metal) -1){
		if($m_metal[$i][0] == 3){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @m_metal) -1){
		if($m_metal[$i][0] == 4){
			my $netID = $h_net{$m_metal[$i][0]."_".$m_metal[$i][0]."_".$m_metal[$i][1]."_".$m_metal[$i][2]."_".$m_metal[$i][3]."_".$m_metal[$i][4]};
			print $out "METAL $m_metal[$i][0] $m_metal[$i][1] $m_metal[$i][2] $m_metal[$i][3] $m_metal[$i][4] $netID\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
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
		if($via_wire[$i][0] == 1 && $via_wire[$i][1] == 2){
			print $out "VIA_WIRE $via_wire[$i][0] $via_wire[$i][1] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
		if($via_wire[$i][0] == 2 && $via_wire[$i][1] == 1){
			print $out "VIA_WIRE $via_wire[$i][1] $via_wire[$i][0] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
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
		if($via_wire[$i][0] == 2 && $via_wire[$i][1] == 3){
			print $out "VIA_WIRE $via_wire[$i][0] $via_wire[$i][1] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
		if($via_wire[$i][0] == 3 && $via_wire[$i][1] == 2){
			print $out "VIA_WIRE $via_wire[$i][1] $via_wire[$i][0] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
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
		if($via_wire[$i][0] == 3 && $via_wire[$i][1] == 4){
			print $out "VIA_WIRE $via_wire[$i][0] $via_wire[$i][1] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
		if($via_wire[$i][0] == 4 && $via_wire[$i][1] == 3){
			print $out "VIA_WIRE $via_wire[$i][1] $via_wire[$i][0] $via_wire[$i][2] $via_wire[$i][3]\r\n";
		}
	}
	for my $i(0 .. (scalar @wire) -1){
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
		if($final_via[$i][0] == 3 && $final_via[$i][1] == 4){
			if(exists($h_wire{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]})){
				my $netID = $h_net{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]};
				print $out "VIA $final_via[$i][0] $final_via[$i][1] $final_via[$i][2] $final_via[$i][3] $netID\r\n";
			}
		}
	}
	for my $i(0 .. (scalar @final_via) -1){
		if($final_via[$i][0] == 2 && $final_via[$i][1] == 3){
			if(exists($h_wire{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]})){
				my $netID = $h_net{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]};
				print $out "VIA $final_via[$i][0] $final_via[$i][1] $final_via[$i][2] $final_via[$i][3] $netID\r\n";
			}
		}
	}
	for my $i(0 .. (scalar @final_via) -1){
		if($final_via[$i][0] == 1 && $final_via[$i][1] == 2){
			if(exists($h_wire{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]})){
				my $netID = $h_net{$final_via[$i][0]."_".$final_via[$i][1]."_".$final_via[$i][2]."_".$final_via[$i][3]."_".$final_via[$i][2]."_".$final_via[$i][3]};
				print $out "VIA $final_via[$i][0] $final_via[$i][1] $final_via[$i][2] $final_via[$i][3] $netID\r\n";
			}
		}
	}
	print "Converting Result Completed!\nOutput : $outfile\n";
}
