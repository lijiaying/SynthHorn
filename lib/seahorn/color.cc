#ifndef __COLOR_HH__
#define __COLOR_HH__

static llvm::cl::opt<bool> ColorEnable("--color", llvm::cl::desc ("Show the colored output"), cl::init (false));

std::string red="";
std::string green="";
std::string yellow="";
std::string blue="";
std::string mag="";
std::string cyan="";
std::string lgray="";
std::string gray="";
std::string lred="";
std::string lgreen="";
std::string lyellow="";
std::string lblue=""; 
std::string lmag="";
std::string lcyan="";

std::string bred="";
std::string bgreen="";
std::string byellow="";
std::string bblue="";
std::string bmag="";
std::string bcyan="";
std::string blgray="";
std::string bgray="";
std::string blred="";
std::string blgreen="";
std::string blyellow="";
std::string blblue=""; 
std::string blmag="";
std::string blcyan="";

std::string normal="";
std::string bold="";
std::string underline="";

void set_color(bool color_enable) {
	if (color_enable)
	{
		red="\e[31;40m";
		green="\e[32;40m";
		yellow="\e[33;40m";
		blue="\e[34;40m";
		mag="\e[35;40m";
		cyan="\e[36;40m";
		lgray="\e[37;40m";
		gray="\e[90;40m";
		lred="\e[91;40m";
		lgreen="\e[92;40m";
		lyellow="\e[93;40m";
		lblue="\e[94;40m"; 
		lmag="\e[95;40m";
		lcyan="\e[96;40m";

		bred="\e[37;41m";
		bgreen="\e[37;42m";
		byellow="\e[37;43m";
		bblue="\e[37;44m";
		bmag="\e[37;45m";
		bcyan="\e[37;46m";
		blgray="\e[37;47m";
		bgray="\e[37;100m";
		blred="\e[37;101m";
		blgreen="\e[37;102m";
		blyellow="\e[37;103m";
		blblue="\e[37;104m"; 
		blmag="\e[37;105m";
		blcyan="\e[37;106m";

		normal="\e[0m";
		bold="\e[1m";
		underline="\e[4m";
	}
	else
	{
		red="";
		green="";
		yellow="";
		blue="";
		mag="";
		cyan="";
		lgray="";
		gray="";
		lred="";
		lgreen="";
		lyellow="";
		lblue=""; 
		lmag="";
		lcyan="";

		bred="";
		bgreen="";
		byellow="";
		bblue="";
		bmag="";
		bcyan="";
		blgray="";
		bgray="";
		blred="";
		blgreen="";
		blyellow="";
		blblue=""; 
		blmag="";
		blcyan="";

		normal="";
		bold="";
		underline="";
	}
}
