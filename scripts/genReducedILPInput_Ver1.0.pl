#! /usr/bin/perl
#
### Revision History : Ver 1.0 #####
# 2019-11-26 Initial Release

use strict 'vars';
use strict 'refs';
use strict 'subs';

use POSIX;
use Cwd;

### Pre-processing ########################################################
my $ARGC        = @ARGV;
my $workdir     = getcwd();
my $outdir      = "$workdir/inputsReducedILP";
my $infile1		= "";
my $infile2		= "";
my $out;
my $outfile		= "";
my $tmp_name	= "";
my $tmp_out		= "";
my $parseStatus = "init";

if ($ARGC != 1) {
    print "\n*** Error:: Wrong CMD";
    print "\n   [USAGE]: ./genReducedILP.pl [Original ILP Input File]\n\n";
    exit(-1);
} else {
    $infile1	= $ARGV[0];
}

if (!-e "./$infile1") {
    print "\n*** Error:: FILE DOES NOT EXIST..\n";
    print "***         $workdir/$infile1\n\n";
    exit(-1);
} else {
	system "mkdir -p $outdir";
	$outfile     = (split /\./, (split /\//, $infile1)[$#_])[0].".lp";
	open ($out, '>', $outdir."/".$outfile);
	print "a   ILP Input File:    $outfile\n";
}

### Read ILP Inputs
open (my $in, "./$infile1");

my %varHash_M = ();
my %varHash_W = ();
my %varHash_N = ();
my %varHash_V = ();
my %varHash_rm = ();
my %varHash_add = ();
my $idx_hash_m = 0;
my $idx_hash_w = 0;
my $idx_hash_n = 0;
my $idx_hash_v = 0;
while (<$in>){
	my $line = $_;
	chomp($line);

	if($line =~ /^(M\S+) = 0$/){
		$varHash_M{$1} = $idx_hash_m;
		$idx_hash_m++;
	}
	elsif($line =~ /^(W\S+) = 0$/){
		$varHash_W{$1} = $idx_hash_w;
		$idx_hash_w++;
	}
	elsif($line =~ /^(N\S+_C\S+_V\S+) = 0$/){
		$varHash_V{$1} = $idx_hash_v;
		$idx_hash_v++;
	}
	elsif($line =~ /^(N\S+) = 0$/){
		$varHash_N{$1} = $idx_hash_n;
		$idx_hash_n++;
	}
}
close($in);
print "a   Removing $idx_hash_m Metal / $idx_hash_w Wire / $idx_hash_v Vertex / $idx_hash_n Edge Unset Variables from Original Inputs!!\n";

open (my $in, "./$infile1");

my $tmp_str = "";
my $inFileStatus = 0;
while (<$in>){
	my $line = $_;
	chomp($line);

	$tmp_str = $line;

	if($line =~ /^\\ ([0-9]+)\./){
		$inFileStatus = $1;
	}
	if($line eq ""){
		print $out "\n";
	}
	elsif($line =~ /^ANS_WL/){
		foreach my $key(keys %varHash_W){
			$key =~ s/([\(\)])/\\$1/g;
			$line =~ s/ - [0-9]+ $key//g;
		}
		$tmp_str = $line;
		$tmp_str =~ s/[ \t]+//g;
		if($tmp_str ne ""){ print $out $line."\n"; }
	}
	elsif($line =~ /^ANS_ML/){
		foreach my $key(keys %varHash_M){
			$key =~ s/([\(\)])/\\$1/g;
			$line =~ s/ - [0-9]+ $key//g;
		}
		$tmp_str = $line;
		$tmp_str =~ s/[ \t]+//g;
		if($tmp_str ne ""){ print $out $line."\n"; }
	}
	elsif($inFileStatus == 1){
		if($line =~ /^[A-Z_0-9]+\(/){
			my @spl = split('\s', $line);
			$tmp_str = "";
			for(my $i=2; $i<=$#spl; $i=$i+2){
				if(!(exists($varHash_W{$spl[$i]}) || exists($varHash_M{$spl[$i]}) || exists($varHash_N{$spl[$i]}))){
					$tmp_str .= " ".$spl[$i-1]." ".$spl[$i];
				}
				if($i==($#spl-2) && ($tmp_str eq "")){
					last;
				}
			}
			if($tmp_str eq ""){
				$varHash_rm{$spl[0]} = 1;
			}
			else{
				$tmp_str = $spl[0].$tmp_str;
				print $out $tmp_str."\n";
			}
		}
		else{
			print $out $line."\n";
		}
	}
	elsif(($inFileStatus > 1 && $inFileStatus < 10) || ($inFileStatus > 10)){
		my @spl = split('\s', $line);
		$tmp_str = "";
		for(my $i=0; $i<=$#spl; $i=$i+2){
			if(!(exists($varHash_W{$spl[$i]}) || exists($varHash_M{$spl[$i]}) || exists($varHash_N{$spl[$i]}))){
				if($i==0){
					$tmp_str = $spl[$i];
				}
				else{
					$tmp_str .= " ".$spl[$i-1]." ".$spl[$i];
				}
			}
			if($i==($#spl-2) && ($tmp_str eq "")){
				last;
			}
		}
		if($tmp_str eq ""){
			$varHash_rm{$spl[0]} = 1;
		}
		$line = $tmp_str;
		$line =~ s/^ \+ //g;
		### Check & Optimize 1 Term Cases
		### 1) TERM <= 0 ==> Remove and Add Unset Definition
		### 2) TERM <= 1 or >= 0 ==> Remove, Already has boolean definition
		if($line =~ /^([A-Za-z_0-9\(\)]+) ([\=<>]+) ([01])$/){
			if($2 eq "<=" && $3 eq "0"){
				$varHash_add{$1} = 1;
			}
			elsif($2 eq "<=" && $3 eq "1"){
				$line = "";
				$tmp_str = "";
			}
			elsif($2 eq ">=" && $3 eq "0"){
				$line = "";
				$tmp_str = "";
			}
		}
		if($tmp_str ne ""){ print $out $line."\n"; }
	}
	elsif($inFileStatus == 10){
		if($line =~ /^Bounds/){
			if($tmp_str ne ""){ print $out $line."\n"; }
			foreach my $key(keys %varHash_add){
				print $out "$key = 0\n";
			}
		}
		elsif($line =~ /^([A-Za-z_0-9\(\)]+) = [-0-9]+$/){
			if(!(exists($varHash_W{$1}) || exists($varHash_M{$1}) || exists($varHash_N{$1}) || exists($varHash_rm{$1}))){
				print $out $line."\n";
			}
		}
		elsif($line =~ /^([A-Za-z_0-9\(\)]+)$/){
			if(!(exists($varHash_W{$1}) || exists($varHash_M{$1}) || exists($varHash_N{$1}) || exists($varHash_rm{$1}))){
				print $out $line."\n";
			}
		}
		else{
			print $out $line."\n";
		}
	}
	else{
		if($tmp_str ne ""){ print $out $line."\n"; }
	}
}
close($in);
close($out);

print "a   1st Removing Completed!! ".(keys %varHash_add)." additional variables should be removed\n";
### Recursively Reduce Variable till no more changes are exist
my $isChange = 0;
my $idx_loop = 0;
my $tmp_str2;
if(keys %varHash_add > 0){
	$isChange = 1;
}
else{
	print "a   Reduced ILP Input File [$outfile] Generated!!\n";
	exit(-1);
}
while($isChange == 1){
	$idx_loop++;
	print "a   Recursively removing additional variables...[iteration = $idx_loop]\n";
	open (my $in, $outdir."/".$outfile.($idx_loop>1?"_".($idx_loop-1):""));
	open ($out, '>', $outdir."/".$outfile."_".$idx_loop);

	my $tmp_str = "";
	my %tmp_Hash_add = ();
	$isChange = 0;
	while (<$in>){
		my $line = $_;
		chomp($line);

		if($line =~ /^\\ ([0-9]+)\./){
			$inFileStatus = $1;
		}
		$tmp_str = $line;
		$tmp_str2 = $line;
		if($line eq ""){
			print $out "\n";
		}
		elsif($line =~ /^ANS_WL/){
			foreach my $key(keys %varHash_add){
				$key =~ s/([\(\)])/\\$1/g;
				$line =~ s/ - [0-9]+ $key//g;
			}
			$tmp_str = $line;
			$tmp_str =~ s/[ \t]+//g;
			if($tmp_str ne ""){ print $out $line."\n"; }
		}
		elsif($line =~ /^ANS_ML/){
			foreach my $key(keys %varHash_add){
				$key =~ s/([\(\)])/\\$1/g;
				$line =~ s/ - [0-9]+ $key//g;
			}
			$tmp_str = $line;
			$tmp_str =~ s/[ \t]+//g;
			if($tmp_str ne ""){ print $out $line."\n"; }
		}
		elsif($inFileStatus == 1){
			if($line =~ /^[A-Z_0-9]+\(/){
				my @spl = split('\s', $line);
				$tmp_str = "";
				for(my $i=2; $i<=$#spl; $i=$i+2){
					if(!(exists($varHash_add{$spl[$i]}))){
						$tmp_str .= " ".$spl[$i-1]." ".$spl[$i];
					}
					if($i==($#spl-2) && ($tmp_str eq "")){
						last;
					}
				}
				if($tmp_str eq ""){
					$varHash_rm{$spl[0]} = 1;
				}
				else{
					$tmp_str = $spl[0].$tmp_str;
					print $out $tmp_str."\n";
				}
			}
			else{
				print $out $line."\n";
			}
		}
		elsif(($inFileStatus > 1 && $inFileStatus < 10) || ($inFileStatus > 10)){
			my @spl = split('\s', $line);
			$tmp_str = "";
			for(my $i=0; $i<=$#spl; $i=$i+2){
				if(!(exists($varHash_add{$spl[$i]}))){
					if($i==0){
						$tmp_str = $spl[$i];
					}
					else{
						$tmp_str .= " ".$spl[$i-1]." ".$spl[$i];
					}
				}
				if($i==($#spl-2) && ($tmp_str eq "")){
					last;
				}
			}
			if($tmp_str eq ""){
				$varHash_rm{$spl[0]} = 1;
			}
			$line = $tmp_str;
			$line =~ s/^ \+ //g;
			### Check & Optimize 1 Term Cases
			### 1) TERM <= 0 ==> Remove and Add Unset Definition
			### 2) TERM <= 1 or >= 0 ==> Remove, Already has boolean definition
			if($line =~ /^([A-Za-z_0-9\(\)]+) ([\=<>]+) ([01])$/){
				if($2 eq "<=" && $3 eq "0"){
					$tmp_Hash_add{$1} = 1;
				}
				elsif($2 eq "<=" && $3 eq "1"){
					$line = "";
					$tmp_str = "";
				}
				elsif($2 eq ">=" && $3 eq "0"){
					$line = "";
					$tmp_str = "";
				}
			}
			if($tmp_str ne ""){ print $out $line."\n"; }
		}
		elsif($inFileStatus == 10){
			if($line =~ /^Bounds/){
				print $out $line."\n";
				foreach my $key(keys %tmp_Hash_add){
					print $out "$key = 0\n";
				}
			}
			elsif($line =~ /^([A-Za-z_0-9\(\)]+) = [-0-9]+$/){
				if(!exists($varHash_rm{$1})){
					print $out $line."\n";
				}
			}
			elsif($line =~ /^([A-Za-z_0-9\(\)]+)$/){
				if(!exists($varHash_rm{$1})){
					print $out $line."\n";
				}
			}
			else{
				print $out $line."\n";
			}
		}
		else{
			if($tmp_str ne ""){ print $out $line."\n"; }
		}
		if((keys %tmp_Hash_add)>0 || $line ne $tmp_str2){
			$isChange = 1;
		}
	}
	close($in);
	close($out);
	%varHash_add = ();
	%varHash_add = %tmp_Hash_add;
}
my $from = $outdir."/".$outfile."_".$idx_loop;
my $to = $outdir."/".$outfile;
system "\\mv $from $to";
$to = $outdir."/".$outfile."_*";
system "\\rm $to";
print "a   Reduced ILP Input File [$outfile] Generated!!\n";
