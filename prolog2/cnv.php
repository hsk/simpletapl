<?php


foreach(glob("results/*.txt") as $name) {
    change($name);
}

foreach(glob("*.pl") as $name) {
    change($name);
}

function change($name) {
    echo "$name\n";
    $s = file_get_contents("$name");
    $s = file_get_contents("../prolog1/$name");
    $keywords = array(
        "tBool"=>"bool",
        "tNat"=>"nat",
        "tUnit"=>"unit",
        "tFloat"=>"float",
        "tString"=>"string",
        "tTop"=>"top",
        "tBot"=>"bot",
        "tVar"=>"var",
        "tArr"=>"arr",
        "tRecord"=>"record",
        "tAll"=>"all",
        "tSome"=>"some",
        "tAbs"=>"abs",
        "tApp"=>"app",
        "tRec"=>"rec",
        "mTrue"=>"true",
        "mFalse"=>"false",
        "mIf"=>"if",
        "mZero"=>"zero",
        "mSucc"=>"succ",
        "mPred"=>"pred",
        "mIsZero"=>"iszero",
        "mUnit"=>"unit",
        "mFloat"=>"float",
        "mTimesfloat"=>"timesfloat",
        "mString"=>"string",
        "mVar"=>"var",
        "mAbs"=>"fn",
        "mApp"=>"app",
        "mLet"=>"let",
        "mFix"=>"fix",
        "mInert"=>"inert",
        "mAscribe"=>"as",
        "mRecord"=>"record",
        "mProj"=>"proj",
        "mTAbs"=>"tfn",
        "mTApp"=>"tapp",
        "mPack"=>"pack",
        "mUnpack"=>"unpack",
        "mUpdate"=>"update",
        "tVariant"=>"variant",
        "tRef"=>"ref",
        "tSource"=>"source",
        "tSink"=>"sink",
        "mZero"=>"zero",
        "mPred"=>"pred",
        "mTag"=>"tag",
        "mCase"=>"case",
        "mRef"=>"ref",
        "mDeref"=>"deref",
        "mAssign"=>"assign",
        "mLoc"=>"loc",
        "mTry"=>"try",
        "mError"=>"error",
        "mFold"=>"fold",
        "mUnfold"=>"unfold",
    );

    foreach($keywords as $k=>$v) {
        $s = preg_replace('/\\b'.$k.'\\b/s',$v,$s);
    }
    file_put_contents($name, $s);
}
