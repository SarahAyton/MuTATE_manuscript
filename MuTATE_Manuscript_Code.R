#############################################################
#                Multi-Target Tree Prototype                #
#############################################################

library(survival)
library(caret)
library(reshape2)
library(matrixStats)
library(stringr)
library(Hmisc)
library(tidyr)
library(MASS)
library(tidyverse)
library(rpart)
library(rpart.plot)
library(dplyr)
library(Rmisc)
library(ggplot2)
library(Metrics)
library(irr)
library(rms)
library(finalfit)

#############################################################
#                Multi-Target Tree Prototype                #
#############################################################

############### Define Evaluation Functions #################

# Evaluation function for continuous outcomes (all feature types)

Cont_Eval <- function(X, m, Z, k, x_train, continuous, quantseq = seq(0,1,0.05), splitmin=floor(nodesize/4)) {
  contFeature <- list("Zk"=colnames(Z)[k], "Ztype"="Continuous", "Xm"=colnames(X)[m], "Xtype"=NA, "Eval"=NA)
  znum <- which( colnames(x_train)==names(Z[k]) )                           # Extract column number of outcome k
  xnum <- which( colnames(x_train)==names(X[m]) )                           # Extract column number of feature m
  Xm <- x_train[complete.cases(x_train[xnum]), c(xnum)]                     # Extract feature m from the sample or subsample and eliminate missing values
  Xtype <- class(Xm)                                                        # Extract feature attributes
  # Find root entropy
  df <- x_train[complete.cases(x_train[,c(xnum,znum)]), c(1:ncol(x_train))]
  root_fit <- lm(df[,(znum)] ~ 1, df)
  Root_Deviance <- deviance(root_fit)
  # Case of Continuous X Feature
  if (Xtype == "numeric" || Xtype == "integer") {
    contFeature$Xtype <- "Continuous"
    l <- sort(unique(Xm) )                                                  # Extract sequence of unique m values (split threshold candidates)
    # Check that split candidates result in partitions with sufficient opservations (n >= 30)
    valcheck <- data.frame(matrix(nrow = length(l), ncol = 3))
    valcheck[,1] <- l
    for (c in 1:length(l)) {
      valcheck[c,2] <- sum(table(Xm[which(Xm < l[c])]))
      valcheck[c,3] <- sum(table(Xm[which(Xm >= l[c])]))
    }
    ln <- valcheck[which(valcheck[,2] >= splitmin & valcheck[,3] >= splitmin),1]  # Define new split candidate list based on above check
    # If there are less than or equal to 100 split candidates, assess all
    if (length(ln) <= 100 & length(ln) > 0 || continuous == "all") {
      ln <- ln
    }
    # If there are more than 100 split candidates, assess quantiles (default: each 5% seq(0,1,0.05))
    if (length(ln) > 100 || continuous == "quantile") {
      ln <- (quantile(ln, probs = quantseq))
    }
    contFeature$Eval <- matrix(nrow = length(ln), ncol = 12)         # Create matrix to store evaluations on each unique m value
    colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
    contFeature$Eval[,1] <- contFeature$Zk
    contFeature$Eval[,2] <- contFeature$Ztype
    contFeature$Eval[,3] <- colnames(X)[m]
    contFeature$Eval[,4] <- contFeature$Xtype
    contFeature$Eval[,5] <- paste(colnames(X)[m],ln,sep=" < ",collapse=NULL)   # Set matrix row names to unique m values
    contFeature$Eval[,6] <- "Deviance"
    if (length(ln) > 0) {
      for (i in 1:length(ln)) {
        split <- ln[i]                                                                                 # Extract threshold value i
        df_left            <- x_train[which(x_train[xnum]<split),c(1:ncol(x_train))]                   # Assess left child node
        left_fit           <- lm(df_left[,(znum)] ~ df_left[,(xnum)], df_left)
        lf                 <- summary(left_fit)
        Left_Deviance      <- deviance(left_fit)
        df_right           <- x_train[which(x_train[xnum]>=split),c(1:ncol(x_train))]                  # Assess right child node
        right_fit          <- lm(df_right[,(znum)] ~ df_right[,(xnum)], df_right)
        rf                 <- summary(right_fit)
        Right_Deviance     <- deviance(right_fit)
        #contFeature$Eval[i,7] <- sum(Left_Deviance, Right_Deviance)                                    # Assess entropy of split
        contFeature$Eval[i,7] <- mean(((nrow(df_left)/nrow(x_train))*Left_Deviance), ((nrow(df_right)/nrow(x_train))*Right_Deviance))                                 # Assess entropy of split
        contFeature$Eval[i,8] <- (Root_Deviance - sum(((nrow(df_left)/nrow(x_train))*Left_Deviance), ((nrow(df_right)/nrow(x_train))*Right_Deviance)))                  # Assess information gain of split
        contFeature$Eval[i,9] <- ((Root_Deviance - sum(((nrow(df_left)/nrow(x_train))*Left_Deviance), ((nrow(df_right)/nrow(x_train))*Right_Deviance)))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- mean(lf$coefficients[2,4], rf$coefficients[2,4])                      # Assess average p-value of split
      }
    }
  }
  # Case of Categorical X Feature
  else {
    if (length(levels(Xm)) == 2) {
      contFeature$Xtype <- "Categorical"
      l     <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l)-1, ncol = 12)         # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l[1],sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "Deviance"
      #For all levels i of feature m, where m has 2 levels:
      fit                <- lm(x_train[,(znum)] ~ x_train[,(xnum)], x_train)
      fsum               <- summary(fit)
      SplitDeviance      <- deviance(fit)
      contFeature$Eval[,7] <- mean(((nrow(x_train[which(x_train[xnum] != l[1]),c(1:ncol(x_train))])/nrow(x_train))*SplitDeviance),((nrow(x_train[which(x_train[xnum]== l[1]),c(1:ncol(x_train))])/nrow(x_train))*SplitDeviance))                                 # Assess entropy of split
      #contFeature$Eval[,7] <- SplitDeviance                                             # Assess entropy of split
      contFeature$Eval[,8] <- (Root_Deviance - ((nrow(x_train[which(x_train[xnum] != l[1]),c(1:ncol(x_train))])/nrow(x_train))*SplitDeviance))                           # Assess information gain of split
      contFeature$Eval[,9] <- ((Root_Deviance - ((nrow(x_train[which(x_train[xnum] != l[1]),c(1:ncol(x_train))])/nrow(x_train))*SplitDeviance))/Root_Deviance)           # Assess proportion information gain of split
      contFeature$Eval[,10] <- (fsum$coefficients[2,4])                                 # Assess average p-value of split
    }
    else if (length(levels(Xm)) > 2) {
      contFeature$Xtype <- "Categorical"
      l     <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l), ncol = 12)         # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l,sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "Deviance"
      #For all levels i of feature m, where m has 2 levels:
      for (i in 1:length(levels(Xm))) {
        split <- l[i]                                                                     # Extract threshold value i
        df_right           <- x_train[which(x_train[xnum] != split),c(1:ncol(x_train))]   # Assess right child node
        right_fit          <- lm(df_right[,(znum)] ~ df_right[,(xnum)], df_right)
        rf                 <- summary(right_fit)
        Right_Deviance     <- deviance(right_fit)
        #contFeature$Eval[i,7] <- (Right_Deviance)                                    # Assess entropy of split
        contFeature$Eval[i,7] <- mean(((nrow(x_train[which(x_train[xnum] != split),c(1:ncol(x_train))])/nrow(x_train))*Right_Deviance),((nrow(x_train[which(x_train[xnum]==split),c(1:ncol(x_train))])/nrow(x_train))*Right_Deviance))                                 # Assess entropy of split
        contFeature$Eval[i,8] <- (Root_Deviance - ((nrow(df_right)/nrow(x_train))*Right_Deviance))                  # Assess information gain of split
        contFeature$Eval[i,9] <- ((Root_Deviance - ((nrow(df_right)/nrow(x_train))*Right_Deviance))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- (rf$coefficients[2,4])                              # Assess average p-value of split
      }
    }
  }
  # Define feature/outcome ranking will be performed based on information gain
  if (!is.na(contFeature$Eval[1])) {
    forRank <- as.numeric(as.character(contFeature$Eval[,8]))
    contFeature$Eval[,11] <- (rank(-forRank))                                             # Define raw ranking (kRank)
    forScale <- as.numeric(as.character(contFeature$Eval[,9]))
    contFeature$Eval[,12] <- scale(forScale)         # Apply standard normal scaling N(0,1) to proportion information gain
  }
  else {
    contFeature$Eval <- NA
  }
  #forRank <- as.numeric(as.character(contFeature$Eval[,8]))
  #contFeature$Eval[,11] <- (rank(-forRank))                                             # Define raw ranking (kRank)
  #forScale <- as.numeric(as.character(contFeature$Eval[,9]))
  #contFeature$Eval[,12] <- scale(forScale)         # Apply standard normal scaling N(0,1) to proportion information gain
  # Output standardized information gain for SplitVars on k to matrix of splitvars rows, and k columns
  return(contFeature$Eval)
}

# Evaluation function for categorical outcomes (all feature types)

Cat_Eval <- function(X, m, Z, k, data, continuous, quantseq = seq(0,1,0.05), splitmin=floor(nodesize/4)) {
  contFeature <- list("Zk"=colnames(Z)[k], "Ztype"="Categorical", "Xm"=colnames(X)[m], "Xtype"=NA, "Eval"=NA)
  znum <- which( colnames(data)==names(Z[k]) )                           # Extract column number of outcome k
  xnum <- which( colnames(data)==names(X[m]) )                           # Extract column number of feature m
  Xm <- data[complete.cases(data[xnum]), c(xnum)]                     # Extract feature m from the sample or subsample and eliminate missing values
  Xtype <- class(Xm)                                                        # Extract feature attributes
  # Find root entropy
  df <- data[complete.cases(data[,c(xnum,znum)]), c(1:ncol(data))]
  rootProb <- table(Z[,k] )/length(Z[,k] )
  rootGini <- (1-sum(rootProb**2))
  # Case of Continuous X Feature
  if (Xtype == "numeric" || Xtype =="integer") {
    contFeature$Xtype <- "Continuous"
    l <- sort(unique(Xm) )                                                  # Extract sequence of unique m values (split threshold candidates)
    # Check that split candidates result in partitions with sufficient opservations (n >= 30)
    valcheck <- data.frame(matrix(nrow = length(l), ncol = 3))
    valcheck[,1] <- l
    for (c in 1:length(l)) {
      valcheck[c,2] <- sum(table(Xm[which(Xm < l[c])]))
      #valcheck[c,2] <- sum(table(data[which(data[m] < l[c]), m]))
      valcheck[c,3] <- sum(table(Xm[which(Xm >= l[c])]))
      #valcheck[c,3] <- sum(table(Xm[which(Xm >= l[c])]))
    }
    ln <- valcheck[which(valcheck[,2] >= splitmin & valcheck[,3] >= splitmin),1]  # Define new split candidate list based on above check
    if (length(ln)>0) {
      # If there are less than or equal to 100 split candidates, assess all
      #if (length(ln) <= 100 || continuous == "all") {
      if (continuous == "all") {
        ln <- ln
      }
      # If there are more than 100 split candidates, assess quantiles (default: each 5% seq(0,1,0.05))
      #else if (length(ln) > 100 || continuous == "quantile") {
      else {
        ln <- (quantile(ln, probs = quantseq))
      }
      contFeature$Eval <- matrix(nrow = length(ln), ncol = 12)                   # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],ln,sep=" < ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "Gini"
      for (i in 1:length(ln)) {
        split     <- ln[i]                                                                                 # Extract threshold value i
        splitvar  <- data$splitvar <- ifelse(data[xnum]<split, "Left", ifelse(data[xnum]>=split, "Right", NA))
        splitnum <- which( colnames(data)=="splitvar" )                           # Extract column number of feature m
        
        base_prob <- table(splitvar)/length(splitvar)
        crosstab  <- table(data[,znum],data[,splitnum])
        crossprob <- prop.table(crosstab,2)
        No_Node_Gini  <- 1-sum(crossprob[,1]**2)                                                          # Assess left child node
        Yes_Node_Gini <- 1-sum(crossprob[,2]**2)                                                          # Assess right child node
        #contFeature$Eval[i,7] <- sum(base_prob * c(No_Node_Gini,Yes_Node_Gini))                           # Assess entropy of split
        contFeature$Eval[i,7] <- mean((base_prob[[1]]*min(crossprob[,1])), (base_prob[[2]]*min(crossprob[,2])))                          # Assess entropy of split
        contFeature$Eval[i,8] <- (rootGini - sum(base_prob * c(No_Node_Gini,Yes_Node_Gini)))              # Assess information gain of split
        contFeature$Eval[i,9] <- ((rootGini - sum(base_prob * c(No_Node_Gini,Yes_Node_Gini)))/rootGini)   # Assess information gain of split
        contFeature$Eval[i,10] <- NA                                                                      # Assess average p-value of split
      }
    }
    else {
      contFeature$Eval <- NA
    }
  }
  # Case of Categorical X Feature
  else {
    if (length(levels(Xm)) == 2) {
      contFeature$Xtype <- "Categorical"
      l <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l)-1, ncol = 12)                     # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l[1],sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "Gini"
      #For all levels i of feature m, where m has 2 levels:
      split     <- l[1]                                                                                 # Extract threshold value i
      splitvar  <- data$splitvar <- ifelse(data[xnum]==split, "Left", ifelse(data[xnum] != split, "Right", NA))
      splitnum <- which( colnames(data)=="splitvar" )                           # Extract column number of feature m
      
      base_prob <- table(splitvar)/length(splitvar)
      #crosstab  <- table(Z[,k],splitvar)
      crosstab  <- table(data[,znum],data[,splitnum])
      crossprob <- prop.table(crosstab,2)
      No_Node_Gini  <- 1-sum(crossprob[,1]**2)                                                          # Assess left child node
      Yes_Node_Gini <- 1-sum(crossprob[,2]**2)                                                          # Assess right child node
      contFeature$Eval[,7] <- mean((base_prob[[1]]*min(crossprob[,1])), (base_prob[[2]]*min(crossprob[,2])))                          # Assess entropy of split
      #contFeature$Eval[,7] <- sum(base_prob * c(No_Node_Gini,Yes_Node_Gini))                           # Assess entropy of split
      contFeature$Eval[,8] <- (rootGini - sum(base_prob * c(No_Node_Gini,Yes_Node_Gini)))              # Assess information gain of split
      contFeature$Eval[,9] <- ((rootGini - sum(base_prob * c(No_Node_Gini,Yes_Node_Gini)))/rootGini)   # Assess information gain of split
      contFeature$Eval[,10] <- NA                                                                      # Assess average p-value of split
    }
    else if (length(levels(Xm)) > 2) {
      contFeature$Xtype <- "Categorical"
      l <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l), ncol = 12)         # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l,sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "Gini"
      #For all levels i of feature m, where m has 2 levels:
      for (i in 1:length(levels(Xm))) {
        split     <- l[i]                                                                                 # Extract threshold value i
        splitvar  <- ifelse(data[xnum]==split, "Left", ifelse(data[xnum] != split, "Right", NA))
        base_prob <- table(splitvar)/length(splitvar)
        crosstab  <- table(Z[,k],splitvar)
        crossprob <- prop.table(crosstab,2)
        No_Node_Gini  <- 1-sum(crossprob[,1]**2)                                                          # Assess left child node
        Yes_Node_Gini <- 1-sum(crossprob[,2]**2)                                                          # Assess right child node
        contFeature$Eval[i,7] <- mean((base_prob[[1]]*min(crossprob[,1])), (base_prob[[2]]*min(crossprob[,2])))                          # Assess entropy of split
        #contFeature$Eval[i,7] <- sum(base_prob * c(No_Node_Gini,Yes_Node_Gini))                           # Assess entropy of split
        contFeature$Eval[i,8] <- (rootGini - sum(base_prob * c(No_Node_Gini,Yes_Node_Gini)))              # Assess information gain of split
        contFeature$Eval[i,9] <- ((rootGini - sum(base_prob * c(No_Node_Gini,Yes_Node_Gini)))/rootGini)   # Assess information gain of split
        contFeature$Eval[i,10] <- NA                                                                      # Assess average p-value of split
      }
    }
  }
  # Define feature/outcome ranking will be performed based on information gain
  if (!is.na(contFeature$Eval[1])) {
    forRank <- as.numeric(as.character(contFeature$Eval[,8]))
    contFeature$Eval[,11] <- (rank(-forRank))                                             # Define raw ranking (kRank)
    forScale <- as.numeric(as.character(contFeature$Eval[,9]))
    contFeature$Eval[,12] <- scale(forScale)         # Apply standard normal scaling N(0,1) to proportion information gain
  }
  else {
    contFeature$Eval <- NA
  }
  # Output standardized information gain for SplitVars on k to matrix of splitvars rows, and k columns
  return(contFeature$Eval)
}

# Evaluation function for event rate outcomes (all feature types)

Count_Eval <- function(X, m, Z, k, data, continuous, quantseq = seq(0,1,0.05), splitmin=floor(nodesize/4)) {
  contFeature <- list("Zk"=colnames(Z)[k], "Ztype"="Event Rate", "Xm"=colnames(X)[m], "Xtype"=NA, "Eval"=NA)
  znum <- which( colnames(data)==names(Z[k]) )                           # Extract column number of outcome k
  xnum <- which( colnames(data)==names(X[m]) )                           # Extract column number of feature m
  Xm <- data[complete.cases(data[xnum]), c(xnum)]                        # Extract feature m from the sample or subsample and eliminate missing values
  Xtype <- class(Xm)                                                     # Extract feature attributes
  # Find root entropy
  df            <- data[complete.cases(data[,c(xnum,znum)]), c(1:ncol(data))]
  m1            <- glm(df[,(znum)] ~ 1, family="poisson")
  Root_Deviance <- abs(mean(residuals(m1, type = "deviance")))
  # Case of Continuous X Feature
  if (Xtype == "numeric" || Xtype =="integer") {
    contFeature$Xtype <- "Continuous"
    l <- sort(unique(Xm) )                                                  # Extract sequence of unique m values (split threshold candidates)
    # Check that split candidates result in partitions with sufficient opservations (n >= 30)
    valcheck <- data.frame(matrix(nrow = length(l), ncol = 3))
    valcheck[,1] <- l
    for (c in 1:length(l)) {
      valcheck[c,2] <- sum(table(Xm[which(Xm < l[c])]))
      valcheck[c,3] <- sum(table(Xm[which(Xm >= l[c])]))
    }
    ln <- valcheck[which(valcheck[,2] >= splitmin & valcheck[,3] >= splitmin),1]  # Define new split candidate list based on above check
    # If there are less than or equal to 100 split candidates, assess all
    if ((length(ln) <= 100 & length(ln) >0) || (length(ln) >0 & continuous == "all")) {
      ln <- ln
      contFeature$Eval <- matrix(nrow = length(ln), ncol = 12)                   # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],ln,sep=" < ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      for (i in 1:length(ln)) {
        split     <- ln[i]                                                                                 # Extract threshold value i
        df_left            <- data[which(data[xnum]<split),c(1:ncol(data))]                   # Assess left child node
        if (nrow(df_left) > 0) {
          #Left_m1            <- glm(df_left[,(znum)] ~ df_left[,(xnum)], family="poisson")
          #Left_m2            <- update(Left_m1, . ~ . - df_left[,(xnum)])
          #Left_LR            <- anova(Left_m2, Left_m1, test = "LRT")
          #Left_Deviance      <- Left_LR$`Resid. Dev`[2]
          
          Left_m1            <- glm(df_left[,(znum)] ~ 1, family="poisson")
          Left_Deviance      <- abs(mean(residuals(Left_m1, type = "deviance")))
        }
        else {
          Left_Deviance <- NA
        }
        df_right           <- data[which(data[xnum]>=split),c(1:ncol(data))]                  # Assess right child node
        if (nrow(df_right) > 0) {
          #Right_m1           <- glm(df_right[,(znum)] ~ df_right[,(xnum)], family="poisson")
          #Right_m2           <- update(Right_m1, . ~ . - df_right[,(xnum)])
          #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
          #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
          
          Right_m1            <- glm(df_right[,(znum)] ~ 1, family="poisson")
          Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
        }
        else {
          Right_Deviance <- NA
        }
        contFeature$Eval[i,7]  <- mean(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance))                                    # Assess entropy of split
        #contFeature$Eval[i,7]  <- sum(Left_Deviance, Right_Deviance)                                    # Assess entropy of split
        contFeature$Eval[i,8]  <- (Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))                  # Assess information gain of split
        contFeature$Eval[i,9]  <- ((Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- NA #mean((Left_LR$`Pr(>Chi)`[2]), (Right_LR$`Pr(>Chi)`[2]))               # Assess average p-value of split
      }
    }
    # If there are more than 100 split candidates, assess quantiles (default: each 5% seq(0,1,0.05))
    else if (length(ln) > 100 || (length(ln) >0 & continuous == "quantile")) {
      ln <- (quantile(ln, probs = quantseq))
      contFeature$Eval <- matrix(nrow = length(ln), ncol = 12)                   # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],ln,sep=" < ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      for (i in 1:length(ln)) {
        split     <- ln[i]                                                                                 # Extract threshold value i
        df_left            <- data[which(data[xnum]<split),c(1:ncol(data))]                   # Assess left child node
        if (nrow(df_left) > 0) {
          #Left_m1            <- glm(df_left[,(znum)] ~ df_left[,(xnum)], family="poisson")
          #Left_m2            <- update(Left_m1, . ~ . - df_left[,(xnum)])
          #Left_LR            <- anova(Left_m2, Left_m1, test = "LRT")
          #Left_Deviance      <- Left_LR$`Resid. Dev`[2]
          
          Left_m1            <- glm(df_left[,(znum)] ~ 1, family="poisson")
          Left_Deviance      <- abs(mean(residuals(Left_m1, type = "deviance")))
        }
        else {
          Left_Deviance <- NA
        }
        df_right           <- data[which(data[xnum]>=split),c(1:ncol(data))]                  # Assess right child node
        if (nrow(df_right) > 0) {
          #Right_m1           <- glm(df_right[,(znum)] ~ df_right[,(xnum)], family="poisson")
          #Right_m2           <- update(Right_m1, . ~ . - df_right[,(xnum)])
          #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
          #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
          
          Right_m1            <- glm(df_right[,(znum)] ~ 1, family="poisson")
          Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
        }
        else {
          Right_Deviance <- NA
        }
        contFeature$Eval[i,7]  <- mean(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance))                                    # Assess entropy of split
        #contFeature$Eval[i,7]  <- sum(Left_Deviance, Right_Deviance)                                    # Assess entropy of split
        contFeature$Eval[i,8]  <- (Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))                  # Assess information gain of split
        contFeature$Eval[i,9]  <- ((Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- NA#mean((Left_LR$`Pr(>Chi)`[2]), (Right_LR$`Pr(>Chi)`[2]))               # Assess average p-value of split
      }
    }
    else {
      contFeature$Eval <- NA
    }
  }
  # Case of Categorical X Feature
  else {
    if (length(levels(Xm)) == 2) {
      contFeature$Xtype <- "Categorical"
      l <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l)-1, ncol = 12)                     # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l[1],sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      #For all levels i of feature m, where m has 2 levels:
      split     <- l[1]                                                                                 # Extract threshold value i
      #Right_m1           <- glm(data[,(znum)] ~ data[,(xnum)], family="poisson")
      #Right_m2           <- update(Right_m1, . ~ . - data[,(xnum)])
      #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
      #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
      
      Right_m1            <- glm(data[,(znum)] ~ 1, family="poisson")
      Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
      
      contFeature$Eval[,7]  <- mean(((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance), ((nrow(data[which(data[xnum]== split),c(1:ncol(data))])/nrow(data))*Right_Deviance))
      #contFeature$Eval[,7]  <- Right_Deviance                                    # Assess entropy of split
      contFeature$Eval[,8]  <- (Root_Deviance - ((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance))                  # Assess information gain of split
      contFeature$Eval[,9]  <- ((Root_Deviance - ((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance))/Root_Deviance)  # Assess proportion information gain of split
      contFeature$Eval[,10] <- NA #(Right_LR$`Pr(>Chi)`[2])                          # Assess average p-value of split
    }
    else if (length(levels(Xm)) > 2) {
      contFeature$Xtype <- "Categorical"
      l <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l), ncol = 12)         # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l,sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      #For all levels i of feature m, where m has 2 levels:
      for (i in 1:length(levels(Xm))) {
        split     <- l[i]                                                                                 # Extract threshold value i
        df_right           <- data[which(data[xnum] != split),c(1:ncol(data))]                  # Assess right child node
        #Right_m1           <- glm(df_right[,(znum)] ~ df_right[,(xnum)], family="poisson")
        #Right_m2           <- update(Right_m1, . ~ . - df_right[,(xnum)])
        #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
        #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
        
        Right_m1            <- glm(df_right[,(znum)] ~ 1, family="poisson")
        Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
        
        contFeature$Eval[i,7]  <- mean(((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance),((nrow(data[which(data[xnum]== split),c(1:ncol(data))])/nrow(data))*Right_Deviance))                                   # Assess entropy of split
        #contFeature$Eval[i,7]  <- Right_Deviance                                    # Assess entropy of split
        contFeature$Eval[i,8]  <- (Root_Deviance - ((nrow(df_right)/nrow(data))*Right_Deviance))                  # Assess information gain of split
        contFeature$Eval[i,9]  <- ((Root_Deviance - ((nrow(df_right)/nrow(data))*Right_Deviance))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- NA #(Right_LR$`Pr(>Chi)`[2])                          # Assess average p-value of split
      }
    }
  }
  if (!is.na(contFeature$Eval[1])) {
    # Define feature/outcome ranking will be performed based on information gain
    forRank <- as.numeric(as.character(contFeature$Eval[,8]))
    contFeature$Eval[,11] <- (rank(-forRank))                                             # Define raw ranking (kRank)
    forScale <- as.numeric(as.character(contFeature$Eval[,9]))
    contFeature$Eval[,12] <- scale(forScale)         # Apply standard normal scaling N(0,1) to proportion information gain
  }
  else {
    contFeature$Eval <- NA
  }
  # Output standardized information gain for SplitVars on k to matrix of splitvars rows, and k columns
  return(contFeature$Eval)
}

# Evaluation function for time-to-event outcomes (all feature types) --> Use Count_Eval for exponentiated tte outcomes

Surv_Eval <- function(X, m, Z, k, data, continuous, quantseq = seq(0,1,0.05), splitmin=floor(nodesize/4)) {
  contFeature <- list("Zk"=colnames(Z)[k], "Ztype"="Event Rate", "Xm"=colnames(X)[m], "Xtype"=NA, "Eval"=NA)
  survvar <- colnames(Z)[k]
  eventvar  <- (unlist(strsplit(survvar, "_")))[4]
  timevar   <- (unlist(strsplit(survvar, "_")))[3]
  numE <- which(colnames(data)==eventvar)
  numT <- which(colnames(data)==timevar)
  E <- data[,numE]
  Tim <- data[,numT]
  xnum <- which( colnames(data)==names(X[m]) )                           # Extract column number of feature m
  znum <- which( colnames(data)==names(Z[k]) )                           # Extract column number of outcome k
  Xm <- data[complete.cases(data[xnum]), c(xnum)]                        # Extract feature m from the sample or subsample and eliminate missing values
  Xtype <- class(Xm)                                                     # Extract feature attributes
  # Find root entropy
  df            <- data[complete.cases(data[,c(xnum,znum)]), c(1:ncol(data))]
  m1            <- survreg(Surv(Tim, E) ~ 1, df, dist="exponential")
  Root_Deviance <- abs(mean(residuals(m1, type="deviance")))
  # Case of Continuous X Feature
  if (Xtype == "numeric" || Xtype =="integer") {
    contFeature$Xtype <- "Continuous"
    l <- sort(unique(Xm) )                                                  # Extract sequence of unique m values (split threshold candidates)
    # Check that split candidates result in partitions with sufficient opservations (n >= 30)
    valcheck <- data.frame(matrix(nrow = length(l), ncol = 3))
    valcheck[,1] <- l
    for (c in 1:length(l)) {
      valcheck[c,2] <- sum(table(Xm[which(Xm < l[c])]))
      valcheck[c,3] <- sum(table(Xm[which(Xm >= l[c])]))
    }
    ln <- valcheck[which(valcheck[,2] >= splitmin & valcheck[,3] >= splitmin),1]  # Define new split candidate list based on above check
    # If there are less than or equal to 100 split candidates, assess all
    if ((length(ln) <= 100 & length(ln) >0) || (length(ln) >0 & continuous == "all")) {
      ln <- ln
      contFeature$Eval <- matrix(nrow = length(ln), ncol = 12)                   # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],ln,sep=" < ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      
      for (i in 1:length(ln)) {
        split     <- ln[i]                                                                                 # Extract threshold value i
        df_left            <- data[which(data[xnum]<split),c(1:ncol(data))]                   # Assess left child node
        
        if (nrow(df_left) > 0) {
          #Left_m1            <- glm(df_left[,(znum)] ~ df_left[,(xnum)], family="poisson")
          #Left_m2            <- update(Left_m1, . ~ . - df_left[,(xnum)])
          #Left_LR            <- anova(Left_m2, Left_m1, test = "LRT")
          #Left_Deviance      <- Left_LR$`Resid. Dev`[2]
          
          Left_m1            <- survreg(Surv(df_left[,(numT)], df_left[,(numE)]) ~ 1, df_left, dist="exponential")
          Left_Deviance      <- abs(mean(residuals(Left_m1, type = "deviance")))
          
        }
        else {
          Left_Deviance <- NA
          
        }
        df_right           <- data[which(data[xnum]>=split),c(1:ncol(data))]                  # Assess right child node
        if (nrow(df_right) > 0) {
          #Right_m1           <- glm(df_right[,(znum)] ~ df_right[,(xnum)], family="poisson")
          #Right_m2           <- update(Right_m1, . ~ . - df_right[,(xnum)])
          #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
          #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
          
          Right_m1            <- survreg(Surv(df_right[,(numT)], df_right[,(numE)]) ~ 1, df_right, dist="exponential")
          Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
          m1       <- survreg(Surv(Tim, E) ~ 1, data, dist="exponential")
          abs(mean(residuals(m1, type="deviance")))
        }
        else {
          Right_Deviance <- NA
        }
        contFeature$Eval[i,7]  <- mean(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance))                                    # Assess entropy of split
        #contFeature$Eval[i,7]  <- sum(Left_Deviance, Right_Deviance)                                    # Assess entropy of split
        contFeature$Eval[i,8]  <- (Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))                  # Assess information gain of split
        contFeature$Eval[i,9]  <- ((Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- NA #mean((Left_LR$`Pr(>Chi)`[2]), (Right_LR$`Pr(>Chi)`[2]))               # Assess average p-value of split
        
      }
    }
    # If there are more than 100 split candidates, assess quantiles (default: each 5% seq(0,1,0.05))
    else if (length(ln) > 100 || (length(ln) >0 & continuous == "quantile")) {
      ln <- (quantile(ln, probs = quantseq))
      contFeature$Eval <- matrix(nrow = length(ln), ncol = 12)                   # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],ln,sep=" < ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      for (i in 1:length(ln)) {
        split     <- ln[i]                                                                                 # Extract threshold value i
        df_left            <- data[which(data[xnum]<split),c(1:ncol(data))]                   # Assess left child node
        if (nrow(df_left) > 0) {
          #Left_m1            <- glm(df_left[,(znum)] ~ df_left[,(xnum)], family="poisson")
          #Left_m2            <- update(Left_m1, . ~ . - df_left[,(xnum)])
          #Left_LR            <- anova(Left_m2, Left_m1, test = "LRT")
          #Left_Deviance      <- Left_LR$`Resid. Dev`[2]
          
          Left_m1            <- survreg(Surv(df_left[,(numT)], df_left[,(numE)]) ~ 1, df_left, dist="exponential")
          Left_Deviance      <- abs(mean(residuals(Left_m1, type = "deviance")))
        }
        else {
          Left_Deviance <- NA
        }
        df_right           <- data[which(data[xnum]>=split),c(1:ncol(data))]                  # Assess right child node
        if (nrow(df_right) > 0) {
          #Right_m1           <- glm(df_right[,(znum)] ~ df_right[,(xnum)], family="poisson")
          #Right_m2           <- update(Right_m1, . ~ . - df_right[,(xnum)])
          #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
          #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
          
          Right_m1            <- survreg(Surv(df_right[,(numT)], df_right[,(numE)]) ~ 1, df_right, dist="exponential")
          Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
        }
        else {
          Right_Deviance <- NA
        }
        contFeature$Eval[i,7]  <- mean(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance))                                    # Assess entropy of split
        contFeature$Eval[i,8]  <- (Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))                  # Assess information gain of split
        contFeature$Eval[i,9]  <- ((Root_Deviance - sum(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance)))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- NA#mean((Left_LR$`Pr(>Chi)`[2]), (Right_LR$`Pr(>Chi)`[2]))               # Assess average p-value of split
      }
    }
    else {
      contFeature$Eval <- NA
    }
  }
  # Case of Categorical X Feature
  else {
    if (length(levels(Xm)) == 2) {
      contFeature$Xtype <- "Categorical"
      l <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l)-1, ncol = 12)                     # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l[1],sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      #For all levels i of feature m, where m has 2 levels:
      split     <- l[1]                                                                                 # Extract threshold value i
      #Right_m1           <- glm(data[,(znum)] ~ data[,(xnum)], family="poisson")
      #Right_m2           <- update(Right_m1, . ~ . - data[,(xnum)])
      #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
      #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
      
      Right_m1            <- survreg(Surv(data[,(numT)], data[,(numE)]) ~ 1, data, dist="exponential")
      Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
      
      contFeature$Eval[,7]  <- mean(((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance),((nrow(data[which(data[xnum]== split),c(1:ncol(data))])/nrow(data))*Right_Deviance))
      #contFeature$Eval[,7]  <- mean(((nrow(df_left)/nrow(data))*Left_Deviance), ((nrow(df_right)/nrow(data))*Right_Deviance))                                    # Assess entropy of split
      #contFeature$Eval[,7]  <- Right_Deviance                                    # Assess entropy of split
      contFeature$Eval[,8]  <- (Root_Deviance - ((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance))                  # Assess information gain of split
      contFeature$Eval[,9]  <- ((Root_Deviance - ((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance))/Root_Deviance)  # Assess proportion information gain of split
      contFeature$Eval[,10] <- NA #(Right_LR$`Pr(>Chi)`[2])                          # Assess average p-value of split
    }
    else if (length(levels(Xm)) > 2) {
      contFeature$Xtype <- "Categorical"
      l <- levels(Xm)
      contFeature$Eval <- matrix(nrow = length(l), ncol = 12)         # Create matrix to store evaluations on each unique m value
      colnames(contFeature$Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy", "Inf_Gain", "Inf_GainProp", "P_Value", "Rank", "Scale")
      contFeature$Eval[,1] <- contFeature$Zk
      contFeature$Eval[,2] <- contFeature$Ztype
      contFeature$Eval[,3] <- colnames(X)[m]
      contFeature$Eval[,4] <- contFeature$Xtype
      contFeature$Eval[,5] <- paste(colnames(X)[m],l,sep=" in ",collapse=NULL)   # Set matrix row names to unique m values
      contFeature$Eval[,6] <- "LR_Test"
      #For all levels i of feature m, where m has 2 levels:
      for (i in 1:length(levels(Xm))) {
        split     <- l[i]                                                                                 # Extract threshold value i
        df_right           <- data[which(data[xnum] != split),c(1:ncol(data))]                  # Assess right child node
        #Right_m1           <- glm(df_right[,(znum)] ~ df_right[,(xnum)], family="poisson")
        #Right_m2           <- update(Right_m1, . ~ . - df_right[,(xnum)])
        #Right_LR           <- anova(Right_m2, Right_m1, test = "LRT")
        #Right_Deviance     <- Right_LR$`Resid. Dev`[2]
        
        Right_m1            <- survreg(Surv(df_right[,(numT)], df_right[,(numE)]) ~ 1, df_right, dist="exponential")
        Right_Deviance      <- abs(mean(residuals(Right_m1, type = "deviance")))
        
        contFeature$Eval[i,7]  <- mean(((nrow(data[which(data[xnum] != split),c(1:ncol(data))])/nrow(data))*Right_Deviance),((nrow(data[which(data[xnum]== split),c(1:ncol(data))])/nrow(data))*Right_Deviance))
        #contFeature$Eval[i,7]  <- ((nrow(df_right)/nrow(data))*Right_Deviance)                                   # Assess entropy of split
        #contFeature$Eval[i,7]  <- Right_Deviance                                    # Assess entropy of split
        contFeature$Eval[i,8]  <- (Root_Deviance - ((nrow(df_right)/nrow(data))*Right_Deviance))                  # Assess information gain of split
        contFeature$Eval[i,9]  <- ((Root_Deviance - ((nrow(df_right)/nrow(data))*Right_Deviance))/Root_Deviance)  # Assess proportion information gain of split
        contFeature$Eval[i,10] <- NA #(Right_LR$`Pr(>Chi)`[2])                          # Assess average p-value of split
      }
    }
  }
  if (!is.na(contFeature$Eval[1])) {
    # Define feature/outcome ranking will be performed based on information gain
    forRank <- as.numeric(as.character(contFeature$Eval[,8]))
    contFeature$Eval[,11] <- (rank(-forRank))                                             # Define raw ranking (kRank)
    forScale <- as.numeric(as.character(contFeature$Eval[,9]))
    contFeature$Eval[,12] <- scale(forScale)         # Apply standard normal scaling N(0,1) to proportion information gain
  }
  else {
    contFeature$Eval <- NA
  }
  # Output standardized information gain for SplitVars on k to matrix of splitvars rows, and k columns
  return(contFeature$Eval)
}

# Evaluation function to run through all targets and features

MultiEval <- function(X, Ztype, data, continuous = "quantile", quantseq = seq(0,1,0.05), wt=NULL, evalmethod = "avgIG", alpha = 0.05, IGcutoff = 0.95, splitmin) {
  Z <- Ztype$Z
  Eval <- matrix(ncol = 12, nrow = 0)
  colnames(Eval) <- c("Zk","Ztype","Xm","Xtype","Split","Eval","SplitEntropy","Inf_Gain","Inf_GainProp","P_Value","Rank","Scale" )
  for (k in 1:length(Z)) {
    #i <- nrow(Eval)
    if (Ztype$Definitions[k]=="Cont") {
      for (m in 1:length(X)) {
        evaltemp <- Cont_Eval(X, m, Z, k, data, continuous, quantseq, splitmin)
        if (!is.na(evaltemp[9])) {
          Eval <- rbind(Eval, evaltemp)
        }
        else {
          Eval <- Eval
        }
      }
    }
    else if (Ztype$Definitions[k]=="Cat") {
      for (m in 1:length(X)) {
        evaltemp <- Cat_Eval(X, m, Z, k, data, continuous, quantseq, splitmin)
        if (!is.na(evaltemp[9])) {
          Eval <- rbind(Eval, evaltemp)
        }
        else {
          Eval <- Eval
        }
      }
    }
    else if (Ztype$Definitions[k]=="Surv") {
      for (m in 1:length(X)) {
        evaltemp <- Surv_Eval(X, m, Z, k, data, continuous, quantseq, splitmin)
        if (!is.na(evaltemp[9])) {
          Eval <- rbind(Eval, evaltemp)
        }
        else {
          Eval <- Eval
        }
      }
    }
    else {
      for (m in 1:length(X)) {
        evaltemp <- Count_Eval(X, m, Z, k, data, continuous, quantseq, splitmin)
        if (!is.na(evaltemp[9])) {
          Eval <- rbind(Eval, evaltemp)
        }
        else {
          Eval <- Eval
        }
      }
    }
  }
  # Define feature/outcome ranking will be performed based on information gain
  # Apply standard normal scaling N(0,1) to proportion information gain
  Eval[,12] <- NA
  if (evalmethod != "partErr") {
    for (k in 1:length(Z)) {
      kScale <- Eval[which(Eval[,1]==names(Z[k])), ]
      if (ncol(data.frame(kScale)) <= 1) {
        kScale <- t(data.frame(kScale))
        forScale <- as.numeric(as.character(kScale[,9]))
        Eval[which(Eval[,1]==names(Z[k])), ][12] <- forScale
      }
      else {
        kScale <- kScale
        forScale <- as.numeric(as.character(kScale[,9]))
        scalelist <- scale(forScale)
        Eval[which(Eval[,1]==names(Z[k])), ][,12] <- scalelist[,1]
      }
    }
  }
  else {
    for (k in 1:length(Z)) {
      kScale <- Eval[which(Eval[,1]==names(Z[k])), ]
      if (ncol(data.frame(kScale)) <= 1) {
        kScale <- t(data.frame(kScale))
        forScale <- as.numeric(as.character(kScale[,7]))
        Eval[which(Eval[,1]==names(Z[k])), ][12] <- forScale
      }
      else {
        kScale <- kScale
        forScale <- as.numeric(as.character(kScale[,7]))
        scalelist <- scale(forScale)
        Eval[which(Eval[,1]==names(Z[k])), ][,12] <- scalelist[,1]
      }
    }
  }
  # Define total ranking (Rank)
  forRank <- as.numeric(as.character(Eval[,12]))
  Eval[,11] <- as.numeric(as.character(Eval[,11]))
  #Eval[,11] <- (rank(-forRank))
  ifelse(evalmethod != "partErr", (Eval[,11] <- (rank(-forRank))), (Eval[,11] <- (rank(forRank))))
  
  df_Eval       <- data.frame(Eval)
  df_Eval$Scale <- as.numeric(as.character(df_Eval$Scale))
  ScaledInfGain         <- dcast(df_Eval, Xm + Split ~ Zk, value.var="Scale")
  #ScaledInfGain$Average <- rowWeightedMeans(as.matrix(ScaledInfGain[,c(3:ncol(ScaledInfGain))]), weights=wt, na.rm=TRUE)
  #ScaledInfGain$Rank    <- rank(-ScaledInfGain$Average) #existing rank def
  
  #Proposed methods to define best splits
  ScaledInfGain$AvgIG   <- rowWeightedMeans(as.matrix(ScaledInfGain[,c(3:ncol(ScaledInfGain))]), weights=wt, na.rm=TRUE)
  ScaledInfGain$MaxIG   <- NA
  #ScaledInfGain$MostIG  <- rowSums(ScaledInfGain[3:(which(names(ScaledInfGain)=="Average")-1)] > IGcutoff) #IGcutoff (0 by default)
  #redefine cutoff by % values observed overall
  #IGcutoff_val <- quantile(gather(ScaledInfGain, target, IG, 3:(which(names(ScaledInfGain)=="AvgIG")-1), factor_key=TRUE)$IG, probs = IGcutoff)[[1]]
  #ScaledInfGain$MostIG  <- rowSums(ScaledInfGain[3:(which(names(ScaledInfGain)=="AvgIG")-1)] > IGcutoff_val) #IGcutoff (0 by default)
  #redefine cutoff by % values observed per target
  tempIGVals <- ScaledInfGain[3:(which(names(ScaledInfGain)=="AvgIG")-1)]
  for (j in 1:ncol(ScaledInfGain[3:(which(names(ScaledInfGain)=="AvgIG")-1)])) {
    IGcutoff_val <- quantile(ScaledInfGain[,(2+j)], probs = IGcutoff, na.rm = TRUE)[[1]]
    tempIGVals[,j] <- ifelse(ScaledInfGain[,(2+j)] >= IGcutoff_val, 1*(ScaledInfGain[,(2+j)]), 0)
    #print(IGcutoff_val)
  }
  ScaledInfGain$MostIG  <- rowSums(tempIGVals)
  #ScaledInfGain$MinAvgPVal  <- (1-(pnorm(ScaledInfGain$Average)))
  ScaledInfGain$AvgPVal  <- (1-(pnorm(ScaledInfGain$AvgIG)))
  ScaledInfGain$MinPVal <- NA
  for (j in 1:nrow(ScaledInfGain)) {
    #ScaledInfGain[j,]$MaxIG   <- max(ScaledInfGain[j, 3:(which(names(ScaledInfGain)=="Average")-1)])
    ScaledInfGain[j,]$MaxIG   <- max(ScaledInfGain[j, 3:(which(names(ScaledInfGain)=="AvgIG")-1)])
    #ScaledInfGain[j,]$MinPVal <- min(1-(pnorm(as.numeric(as.character(ScaledInfGain[j, 3:(which(names(ScaledInfGain)=="Average")-1)])))))
    ScaledInfGain[j,]$MinPVal <- min(1-(pnorm(as.numeric(as.character(ScaledInfGain[j, 3:(which(names(ScaledInfGain)=="AvgIG")-1)])))))
  }
  ScaledInfGain$MostPVal    <- NA
  ScaledInfGain$AvgMostPVal <- NA
  #for (l in 1:ncol(ScaledInfGain[3:(which(names(ScaledInfGain)=="Average")-1)])) {
  tempPVals <- tempPValsSig <- ScaledInfGain[3:(which(names(ScaledInfGain)=="AvgIG")-1)]
  for (l in 1:ncol(ScaledInfGain[3:(which(names(ScaledInfGain)=="AvgIG")-1)])) {
    #tempPVals <- ScaledInfGain[3:(which(names(ScaledInfGain)=="AvgIG")-1)]
    if (!is.na(sum(ScaledInfGain[,(2+l)]))) {
      vals <- ScaledInfGain[,(2+l)]
      tempPVals[,l] <- 1-pnorm(vals)
      for (r in 1:nrow(tempPVals)) {
        if (tempPVals[r,l] <= alpha) {
          tempPValsSig[r,l] <- tempPVals[r,l]
        }
        else {
          tempPValsSig[r,l] <- NA
        }
      }
    }
    else {
      next
    }
  }
  ScaledInfGain$MostPVal    <- rowSums(tempPVals <= alpha) #alpha (0.05 by default)
  ScaledInfGain$AvgMostPVal <- rowMeans(tempPValsSig, na.rm = TRUE)
  ScaledInfGain$InvMinPVal  <- (1 - ScaledInfGain$AvgMostPVal)
  ScaledInfGain$WtMinPval   <- (ScaledInfGain$InvMinPVal)*(ScaledInfGain$MostPVal)
  #heatdf$Scale <- as.numeric(as.character(heatdf$Scale))
  #heatdf$P_Value <- 1-(pnorm(heatdf$Scale))
  if (evalmethod == "maxIG") {
    ScaledInfGain$Rank    <- rank(-ScaledInfGain$MaxIG) #Maximum information gain on any one target
  }
  else if (evalmethod == "mostIG") {
    ScaledInfGain$Rank    <- rank(-ScaledInfGain$MostIG) #Most number of meaningful (>= IGcutoff) targets
  }
  else if (evalmethod == "avgPVal") {
    if (all(is.na(ScaledInfGain$AvgMostPVal))) {
      ScaledInfGain$Rank    <- rank(ScaledInfGain$AvgPVal) #Average p-value of all significant (<= alpha) targets
    }
    # If no targets are significant --> avg. sig = NA --> default to avg. p-val
    else {
      ScaledInfGain$Rank    <- rank(ScaledInfGain$AvgMostPVal) #Average p-value of all significant (<= alpha) targets
    }
  }
  else if (evalmethod == "minPVal") {
    #ScaledInfGain$Rank    <- rank(ScaledInfGain$MinPVal) #existing rank def
    if (all(is.na(ScaledInfGain$AvgMostPVal))) {
      ScaledInfGain$Rank    <- rank(ScaledInfGain$MinPVal)
    }
    # If no targets are significant --> avg. sig = NA --> default to min. p-val
    else {
      ScaledInfGain$Rank    <- rank(-ScaledInfGain$WtMinPval) #Average target-weighted p-value of all significant targets
    }
  }
  else if (evalmethod == "mostPVal") {
    if (all(is.na(ScaledInfGain$AvgMostPVal))) {
      ScaledInfGain$Rank    <- rank(ScaledInfGain$MostIG)
    }
    # If no targets are significant --> avg. sig = NA --> default to most targets with IG >= IGcutoff
    else {
      ScaledInfGain$Rank    <- rank(-ScaledInfGain$MostPVal) #Average target-weighted p-value of all significant targets
    }
  }
  else if (evalmethod == "partErr") {
    ScaledInfGain$Rank    <- rank(ScaledInfGain$AvgIG) #Most information gain (average) across targets
  }
  else {
    #ScaledInfGain$Rank    <- rank(-ScaledInfGain$Average) #existing rank def
    ScaledInfGain$Rank    <- rank(-ScaledInfGain$AvgIG) #Most information gain (average) across targets
  }
  return(list(Eval, ScaledInfGain))
}

# Function to assess all targets (%, counts, proportions, etc.) at a given node

MTSummary <- function(targets=Ztype, data) {#enter dataframe and outcomes
  MT <- as.list(1:((length(colnames(targets[[2]])))))
  names(MT) <- c(colnames(targets[[2]]))
  for (i in 1:length(targets$Definitions)) {
    if (targets$Definitions[i] =="Cat") {
      Z <- targets$Z[,i]
      Zname    <- colnames(targets$Z)[i]
      num <- which(colnames(data)==Zname)
      
      missingZ <- sum(is.na (data[which(colnames(data)==Zname)]))
      countsZ  <- table(Z)
      propZ    <- prop.table(countsZ)
      
      #dataX <- data[which(!is.na(data[,c(colnames(data)==Zname)])), c(1:ncol(data))]
      #dataX <- dataX[ , colSums(is.na(dataX)) == 0]
      #varlev <- paste((names(propZ[(propZ)>=max(propZ)])))
      #varnum <- which(colnames(dataX)==Zname)
      #dataX$Zvar <- as.factor(ifelse(dataX[,c(varnum)]==varlev, 1, 0))
      
      #set.seed(123)
      #n.folds <- 10
      #folds   <- cut(sample(seq_len(nrow(dataX))),  breaks=n.folds, labels=FALSE) # Note!
      #dataX$folds <- folds
      #all.confustion.tables <- list()
      #for (j in seq_len(n.folds)) {
      #  train <- dataX[which(dataX$folds !=j), c(1:ncol(dataX))]  # Take all other samples than i
      #  test <- dataX[which(dataX$folds ==j), c(1:ncol(dataX))]  # Take all other samples than i
      #  glm.train <- glm(Zvar ~ 1, family = binomial, data = train)
      #  logit.prob <- predict(glm.train, newdata = test)
      #  pred.class <- ifelse(logit.prob < 0, 0, 1)
      #  all.confustion.tables[[j]] <- table(pred = pred.class, true = test$Zvar)
      #}
      #misclassrisk <- function(x) { (sum(x) - sum(diag(x)))/sum(x) }
      #risk <- sapply(all.confustion.tables, misclassrisk )
      
      vardata           <- (as.list(1:(3+2*(length(levels(Z))))))
      vardata_names     <- as.list(1:(3+2*(length(levels(Z)))))
      vardata_names[1]  <- c("absent")
      vardata[(1)]    <- ((missingZ))
      for (j in 1:length(levels(as.factor(Z)))) {
        vardata[(j*2)]          <- (countsZ[[j]])
        vardata[(j*2+1)]        <- (round(propZ[[j]], 4))
        vardata_names[(j*2)]   <- (paste(levels(Z)[j],"count",sep = "_"))
        vardata_names[(j*2+1)] <- (paste(levels(Z)[j],"prop",sep = "_"))
      }
      vardata[(2+2*(length(levels(Z))))] <- paste(names(propZ[(propZ)>=max(propZ)]))
      vardata_names[(2+2*(length(levels(Z))))]  <- c("predicted")
      vardata[(3+2*(length(levels(Z))))] <- (round(1-max(propZ),4))
      vardata_names[(3+2*(length(levels(Z))))]  <- c("expectedloss")
      #vardata_names[(4+2*(length(levels(Z))))]  <- c("Xerror")
      #vardata[(4+2*(length(levels(Z))))]        <- as.numeric(1 - round(mean(risk),4))
      #vardata_names[(5+2*(length(levels(Z))))]  <- c("Xstd")
      #vardata[(5+2*(length(levels(Z))))]        <- as.numeric(round(sd(risk),4))
      names(vardata)  <- vardata_names
      
      MT[[i]] <- as.list(1:(3+2*(length(levels(as.factor(Z))))))
      MT[[i]] <- vardata
    }
    else if (targets$Definitions[i] =="Surv") {
      survvar <- colnames(targets$Z)[i]
      Zname   <- (unlist(strsplit(survvar, "_")))[4]
      eventvar  <- (unlist(strsplit(survvar, "_")))[4]
      timevar   <- (unlist(strsplit(survvar, "_")))[3]
      num <- which(colnames(data)==Zname)
      numE <- which(colnames(data)==eventvar)
      numT <- which(colnames(data)==timevar)
      Z <- as.numeric(as.character(data[,num]))
      E <- data[,numE]
      Tim <- data[,numT]
      
      missingZ <- sum(is.na (Z))
      sumcheck <- sum(Z)
      countsZ  <- table(Z)
      propZ    <- prop.table(countsZ)
      #m1       <- glm(Z ~ 1, family="poisson", data)
      
      #fit <- rpart(Surv(daystolastordeath, death) ~ ., data = x_train, method="exp", cp=0.1)
      #fit <- rpart(daystolastordeath ~ ., data = x_train, method="poisson", cp=0.1)
      #m1       <- survreg(Surv(data$daystolastordeath, data$death01) ~ 1, dist="exponential")
      
      m1       <- survreg(Surv(Tim, E) ~ 1, data, dist="exponential")
      #m1stats  <- summary(survfit(Surv(Tim, E) ~ 1, data), times = 365.25)
      
      #dataX <- data[which(!is.na(data[,c(colnames(data)==survvar)])), c(1:ncol(data))]
      #dataX <- dataX[ , colSums(is.na(dataX)) == 0]
      #ZnameX   <- colnames(targets$Z)[i]
      #ZnumX <- which(colnames(dataX)==survvar)
      #dataX$Zvar <- dataX[,c(ZnumX)]
      
      #set.seed(123)
      #n.folds <- 10
      #folds   <- cut(sample(seq_len(nrow(dataX))),  breaks=n.folds, labels=FALSE) # Note!
      #dataX$folds <- folds
      #err <- std <- as.list(1:n.folds)
      #for (j in seq_len(n.folds)) {
      #  train <- dataX[which(dataX$folds !=j), c(1:ncol(dataX))]  # Take all other samples than i
      #  test <- dataX[which(dataX$folds ==j), c(1:ncol(dataX))]  # Take all other samples than i
      #  glm.train <- glm(Zvar ~ 1, family = poisson, data = train)
      #  pois.prob <- predict(glm.train, newdata = test, type = "response", se.fit=TRUE)
      #  err_eval <- eval(pois.prob, glm.train)
      #  err[[j]] <- mean(err_eval$fit)
      #  std[[j]] <- mean(err_eval$se.fit)
      #}
      
      vardata           <- as.list(1:4)
      vardata_names     <- as.list(1:4)
      vardata_names[1]  <- c("absent")
      vardata[(1)]      <- ((missingZ))
      vardata_names[2]  <- c("events_count")
      vardata[2]        <- ifelse(sumcheck > 0 & length(countsZ) > 1, (countsZ[[2]]), 0)
      vardata_names[3]  <- c("estimatedrate")
      #vardata[3]        <- m1stats$surv
      vardata[3]        <- ifelse(sumcheck > 0 & length(propZ) > 1, (propZ[[2]]), 0)
      vardata_names[4]  <- c("deviance")
      vardata[4]        <- abs(mean(residuals(m1, type="deviance")))
      #vardata[4]        <- m1$deviance
      
      #vardata_names[5]  <- c("Xerror")
      #vardata[5]        <- (round(mean(as.numeric(err)),4))
      #vardata_names[6]  <- c("Xstd")
      #vardata[6]        <- (round(mean(as.numeric(std)),4))
      names(vardata)    <- vardata_names
      
      MT[[i]] <- as.list(1:4)
      MT[[i]] <- vardata
    }
    else if (targets$Definitions[i] =="Count") {
      Zname    <- colnames(targets$Z)[i]
      num      <- which(colnames(data)==Zname)
      Z <- data[,num]
      
      missingZ <- sum(is.na (data[which(colnames(data)==Zname)]))
      countsZ  <- sum(Z)
      propZ    <- mean(Z)
      m1       <- glm(Z ~ 1, family="poisson", data)
      
      #dataX <- data[which(!is.na(data[,c(colnames(data)==Zname)])), c(1:ncol(data))]
      #dataX <- dataX[ , colSums(is.na(dataX)) == 0]
      #ZnumX <- which(colnames(dataX)==Zname)
      #dataX$Zvar <- dataX[,c(ZnumX)]
      
      #set.seed(123)
      #n.folds <- 10
      #folds   <- cut(sample(seq_len(nrow(dataX))),  breaks=n.folds, labels=FALSE) # Note!
      #dataX$folds <- folds
      #err <- std <- as.list(1:n.folds)
      #for (j in seq_len(n.folds)) {
      #  train <- dataX[which(dataX$folds !=j), c(1:ncol(dataX))]  # Take all other samples than i
      #  test <- dataX[which(dataX$folds ==j), c(1:ncol(dataX))]  # Take all other samples than i
      #  glm.train <- glm(Zvar ~ 1, family = poisson, data = train)
      #  pois.prob <- predict(glm.train, newdata = test, type = "response", se.fit=TRUE)
      #  err_eval <- eval(pois.prob, glm.train)
      #  err[[j]] <- mean(err_eval$fit)
      #  std[[j]] <- mean(err_eval$se.fit)
      #}
      
      vardata           <- as.list(1:4)
      vardata_names     <- as.list(1:4)
      vardata_names[1]  <- c("absent")
      vardata[(1)]      <- ((missingZ))
      vardata_names[2]  <- c("events_count")
      vardata[2]        <- countsZ
      vardata_names[3]  <- c("estimatedrate")
      vardata[3]        <- propZ
      vardata_names[4]  <- c("deviance")
      vardata[4]        <- abs(mean(residuals(m1, type = "deviance")))
      #vardata[4]        <- m1$deviance
      #vardata_names[5]  <- c("Xerror")
      #vardata[5]        <- (round(mean(as.numeric(err)),4))
      #vardata_names[6]  <- c("Xstd")
      #vardata[6]        <- (round(mean(as.numeric(std)),4))
      names(vardata)    <- vardata_names
      
      MT[[i]] <- as.list(1:4)
      MT[[i]] <- vardata
    }
    else {
      Z <- targets$Z[,i]
      Zname    <- colnames(targets$Z)[i]
      num      <- which(colnames(data)==Zname)
      
      missingZ <- sum(is.na (Z))
      summaryZ <- summary(Z)
      model <- lm(Z~1, data)
      model_summ <-summary(model)
      #summary(lm(Z~1, data))$r.squared
      #summary(lm(Z~1, data))$adj.r.squared
      #RMSE <- sqrt(c(crossprod(model$residuals)) / length(model$residuals))
      #dataX <- data[which(!is.na(data[,c(colnames(data)==Zname)])), c(1:ncol(data))]
      #dataX <- dataX[ , colSums(is.na(dataX)) == 0]
      #ZnumX <- which(colnames(dataX)==Zname)
      #dataX$Zvar <- dataX[,c(ZnumX)]
      
      #set.seed(123)
      #n.folds <- 10
      #folds   <- cut(sample(seq_len(nrow(dataX))),  breaks=n.folds, labels=FALSE) # Note!
      #dataX$folds <- folds
      #Xerror <- Xstd <- as.list(1:n.folds)
      #for (j in seq_len(n.folds)) {
      #  train <- dataX[which(dataX$folds !=j), c(1:ncol(dataX))]  # Take all other samples than i
      #  test <- dataX[which(dataX$folds ==j), c(1:ncol(dataX))]  # Take all other samples than i
      #  glm.train <- glm(Zvar ~ 1, family = gaussian, data = train)
      #  lin.prob <- predict(glm.train, newdata = test)
      #  rss <- sum((test$Zvar - lin.prob) ^ 2)
      #  tss <- sum((test$Zvar - mean(test$Zvar)) ^ 2)
      #  Rsquared[[j]] <- (1 - ((rss)/(tss)) )
      #}
      
      vardata           <- as.list(1:6)
      vardata_names     <- as.list(1:6)
      vardata_names[1]  <- c("absent")
      vardata[(1)]      <- ((missingZ))
      vardata_names[2]  <- c("mean")
      vardata[2]        <- round(summaryZ[[4]], 4)
      vardata_names[3]  <- c("median")
      vardata[3]        <- round(summaryZ[[3]], 4)
      vardata_names[4]  <- c("IQR25")
      vardata[4]        <- round(summaryZ[[2]],4)
      vardata_names[5]  <- c("IQR75")
      vardata[5]        <- round(summaryZ[[5]],4)
      vardata_names[6]  <- c("MSE")
      vardata[6]        <- round((mean(model_summ$residuals^2)),4)
      #vardata_names[7]  <- c("Xerror")
      #vardata[7]        <- (1-round(abs(mean(Rsquared)),4))
      #vardata_names[8]  <- c("Xstd")
      #vardata[8]        <- (round(sd(abs(Rsquared)),4))
      names(vardata)    <- vardata_names
      
      MT[[i]] <- as.list(1:6)
      MT[[i]] <- vardata
    }
  }
  return(MT)
}

# Function to assess cross-validated error and SD for any given partition

CVsplitEval <- function(splitvar, X, targets, data) {#enter dataframe and outcomes
  MT <- as.list(1:((length(colnames(targets[[2]])))))
  names(MT) <- c(colnames(targets[[2]]))
  var       <- (unlist(strsplit(splitvar, " ")))[1]
  varnum    <- which(colnames(data)==var)
  notation  <- (unlist(strsplit(splitvar, " ")))[2]
  thresh    <- str_remove(splitvar, var)
  ifelse(notation == "in", threshold <- str_remove(thresh, " in "),
         ifelse(notation == "<", threshold <- str_remove(thresh, " < "), NA))
  ifelse(notation == "in", (data$binrule <- as.factor(ifelse(data[,(varnum)] == threshold, "yes", "no"))),
         (data$binrule <- as.factor(ifelse(data[,(varnum)] < as.numeric(threshold), "yes", "no"))))
  if (notation == "in") {
    data$binrule <- as.factor(ifelse(data[,(varnum)] == threshold, "yes", "no"))
  }
  else { data$binrule <- as.factor(ifelse(data[,(varnum)] < threshold, "yes", "no")) }
  #binnum    <- which(colnames(data)=="binrule")
  start <- Sys.time()
  for (i in 1:length(targets$Definitions)) {
    if (targets$Definitions[i] =="Cat") {
      Z <- targets$Z[,i]
      Zname    <- colnames(targets$Z)[i]
      Zvarnum    <- which(colnames(data)==Zname)
      propZ    <- prop.table(table(Z))
      
      dataX <- data[which(!is.na(data[,c(colnames(data)==Zname)])), c(1:ncol(data))]
      dataX <- data.frame(data[, c(Zvarnum, ncol(data))])
      #dataX <- data[which(!is.na(data[,c(colnames(data)==binrule)])), c(1:ncol(data))]
      #dataX <- dataX[ , colSums(is.na(dataX)) == 0]
      dataX <- dataX[complete.cases(dataX),]
      varlev <- paste((names(propZ[(propZ)>=max(propZ)])))
      #Zvarnum <- which(colnames(dataX)==Zname)
      dataX$Zvar <- as.factor(dataX[,1])
      
      set.seed(123)
      #train.control <- trainControl(method = "cv", number = 10)
      #model <- train(Zvar ~ binrule, data = (dataX[complete.cases(dataX),]), method = "glm", family="binomial", trControl = train.control)
      model_b <- glm(Zvar ~ binrule, family="binomial", data = (dataX))
      Accuracy <- accuracy(dataX[complete.cases(dataX),]$Zvar, predict(model_b))
      
      set1 <- dataX[complete.cases(dataX),]$Zvar
      set2 <- predict(model_b)
      set  <- cbind(set1, set2)
      Kappa    <- (kappa2(set))$value
      
      vardata           <- as.list(1:4)
      #vardata[(1)]      <- model$results[[2]]
      #vardata[(2)]      <- model$results[[4]]
      #vardata[(3)]      <- model$results[[3]]
      #vardata[(4)]      <- model$results[[5]]
      
      vardata[(1)]      <- Accuracy
      vardata[(2)]      <- NA
      vardata[(3)]      <- Kappa
      vardata[(4)]      <- NA
      names(vardata)    <- c("Accuracy","AccuracySD","Kappa","KappaSD")
      
      MT[[i]] <- as.list(1:4)
      MT[[i]] <- vardata
    }
    else if (targets$Definitions[i] =="Surv") {
      #survvar <- colnames(targets$Z)[i]
      
      #dataX <- data[which(!is.na(data[,c(colnames(data)==survvar)])), c(1:ncol(data))]
      #dataX <- dataX[ , colSums(is.na(dataX)) == 0]
      #ZnumX <- which(colnames(dataX)==survvar)
      #dataX$Zvar <- dataX[,c(ZnumX)]
      
      Z <- targets$Z[,i]
      Zname    <- colnames(targets$Z)[i]
      Zvarnum    <- which(colnames(data)==Zname)
      
      dataX <- data[which(!is.na(data[,c(colnames(data)==Zname)])), c(1:ncol(data))]
      dataX <- data.frame(data[, c(Zvarnum, ncol(data))])
      dataX <- dataX[complete.cases(dataX),]
      dataX$Zvar <- (dataX[,1])
      
      set.seed(123)
      #train.control <- trainControl(method = "cv", number = 10)
      #model <- train(Zvar ~ binrule, data = (dataX[complete.cases(dataX),]), method = "glm", family="poisson", trControl = train.control)
      
      model_b <- glm(Zvar ~ binrule, family="poisson", data = (dataX[complete.cases(dataX),]))
      
      RMSE <- rmse(dataX[complete.cases(dataX),]$Zvar, predict(model_b))
      MAE  <- mae(dataX[complete.cases(dataX),]$Zvar, predict(model_b))
      Rsquared <- 1 - model_b$deviance/model_b$null.deviance
      
      vardata           <- as.list(1:6)
      #vardata[(1)]      <- model$results[[2]]
      #vardata[2]        <- model$results[[5]]
      #vardata[3]        <- model$results[[3]]
      #vardata[4]        <- model$results[[6]]
      #vardata[5]        <- model$results[[4]]
      #vardata[6]        <- model$results[[7]]
      
      vardata[(1)]      <- RMSE
      vardata[2]        <- NA
      vardata[3]        <- Rsquared
      vardata[4]        <- NA
      vardata[5]        <- MAE
      vardata[6]        <- NA
      names(vardata)    <- c("RMSE","RMSESD","Rsquared","RsquaredSD","MAE","MAESD")
      
      MT[[i]] <- as.list(1:6)
      MT[[i]] <- vardata
    }
    else if (targets$Definitions[i] =="Count") {
      Z <- targets$Z[,i]
      Zname    <- colnames(targets$Z)[i]
      Zvarnum    <- which(colnames(data)==Zname)
      
      dataX <- data[which(!is.na(data[,c(colnames(data)==Zname)])), c(1:ncol(data))]
      dataX <- data.frame(data[, c(Zvarnum, ncol(data))])
      dataX <- dataX[complete.cases(dataX),]
      dataX$Zvar <- (dataX[,1])
      
      set.seed(123)
      #train.control <- trainControl(method = "cv", number = 10)
      #model <- train(Zvar ~ binrule, data = (dataX[complete.cases(dataX),]), method = "glm", family="binomial", trControl = train.control)
      model_b <- glm(Zvar ~ binrule, family="poisson", data = (dataX[complete.cases(dataX),]))
      
      RMSE <- rmse(dataX[complete.cases(dataX),]$Zvar, predict(model_b))
      MAE  <- mae(dataX[complete.cases(dataX),]$Zvar, predict(model_b))
      Rsquared <- 1 - model_b$deviance/model_b$null.deviance
      
      vardata           <- as.list(1:6)
      #vardata[(1)]      <- model$results[[2]]
      #vardata[2]        <- model$results[[5]]
      #vardata[3]        <- model$results[[3]]
      #vardata[4]        <- model$results[[6]]
      #vardata[5]        <- model$results[[4]]
      #vardata[6]        <- model$results[[7]]
      
      vardata[(1)]      <- RMSE
      vardata[2]        <- NA
      vardata[3]        <- Rsquared
      vardata[4]        <- NA
      vardata[5]        <- MAE
      vardata[6]        <- NA
      names(vardata)    <- c("RMSE","RMSESD","Rsquared","RsquaredSD","MAE","MAESD")
      
      MT[[i]] <- as.list(1:6)
      MT[[i]] <- vardata
    }
    else {
      Zname    <- colnames(targets$Z)[i]
      
      dataX <- data[which(!is.na(data[,c(colnames(data)==Zname)])), c(1:ncol(data))]
      dataX <- dataX[ , colSums(is.na(dataX)) == 0]
      ZnumX <- which(colnames(dataX)==Zname)
      dataX$Zvar <- dataX[,c(ZnumX)]
      
      set.seed(123)
      #train.control <- trainControl(method = "cv", number = 10)
      #model <- train(Zvar ~ binrule, data = (dataX[complete.cases(dataX),]), method = "lm", trControl = train.control)
      
      model_b <- glm(Zvar ~ binrule, data = (dataX[complete.cases(dataX),]), family = gaussian)
      
      RMSE <- rmse(dataX[complete.cases(dataX),]$Zvar, predict(model_b))
      MAE  <- mae(dataX[complete.cases(dataX),]$Zvar, predict(model_b))
      Rsquared <- 1 - model_b$deviance/model_b$null.deviance
      
      vardata           <- as.list(1:6)
      #vardata[(1)]      <- model$results[[2]]
      #vardata[2]        <- model$results[[5]]
      #vardata[3]        <- model$results[[3]]
      #vardata[4]        <- model$results[[6]]
      #vardata[5]        <- model$results[[4]]
      #vardata[6]        <- model$results[[7]]
      
      vardata[(1)]      <- RMSE
      vardata[2]        <- NA
      vardata[3]        <- Rsquared
      vardata[4]        <- NA
      vardata[5]        <- MAE
      vardata[6]        <- NA
      names(vardata)    <- c("RMSE","RMSESD","Rsquared","RsquaredSD","MAE","MAESD")
      
      MT[[i]] <- as.list(1:6)
      MT[[i]] <- vardata
    }
  }
  end <- Sys.time()
  difftime(end, start)
  return(MT)
}

# Function to clean datasets prior to partitioning at each iteration

SplitPrep <- function(Xdf, df, data_splt, parentsplit) {
  # Drop any unused factor levels in subset
  #if(exists("droplist")){
  #  rm(droplist)
  #}
  df <- data.frame(df)
  splitX_df     <- droplevels(data.frame(Xdf), c(1:ncol(data.frame(Xdf))))
  split_data_df <- droplevels(data.frame(df),  c(1:ncol(data.frame(df))))
  for (n in 1:ncol(data.frame(splitX_df))) {
    # If the X-var was used in the parent split:
    if (!is.null(data.frame(splitX_df)[,c(n)]) & colnames(data.frame(splitX_df))[(n)] == parentsplit) {
      # if the droplist does exist, append additional variables with only one level
      if (exists("droplist")){
        droplist <- c(droplist, n)
      }
      # if the droplist doesn't exist, create it
      else {
        droplist <- c(n)
      }
    }
    # If the X-var is categorical:
    else if (!is.null(data.frame(splitX_df)[,c(n)]) & class(data.frame(splitX_df)[,c(n)]) == "factor") {
      # If the X-var has < 2 levels, remove it from split candidates
      if (length(levels(data.frame(splitX_df)[,c(n)])) < 2) {
        # if the droplist does exist, append additional variables with only one level
        if (exists("droplist")){
          droplist <- c(droplist, n)
        }
        # if the droplist doesn't exist, create it
        else {
          droplist <- c(n)
        }
      }
      # If the X-var has a prevalence in < 5% of observations in that node, remove it from split candidates
      else if (!is.null(table(data.frame(splitX_df)[,c(n)])) & (min(table(data.frame(splitX_df)[,c(n)])) < (0.05*nrow(data_splt)))) {
        # if the droplist does exist, append additional variables with less than 5% level prevalence
        if (exists("droplist")){
          droplist <- c(droplist, n)
        }
        # if the droplist doesn't exist, create it
        else {
          droplist <- c(n)
        }
      }
      # Otherwise, keep all split candidates
      else {
        # if the droplist does exist, append additional variables with less than 5% level prevalence
        if (exists("droplist")){
          droplist <- (droplist)
        }
        # if the droplist doesn't exist, create it
        else {
          droplist <- (NA)
          rm(droplist)
        }
      }
    }
    # If the X-var is continuous: only keep those with at least two observed values as split candidates
    else {
      if (!is.null(data.frame(splitX_df)[,c(n)]) & length(unique(data.frame(splitX_df)[,c(n)])) < 2) {
        # if the droplist does exist, append additional variables with only one value
        if (exists("droplist")){
          droplist <- c(droplist, n)
        }
        # if the droplist doesn't exist, create it
        else {
          droplist <- c(n)
        }
      }
      else {
        # if the droplist does exist, append additional variables with less than 5% level prevalence
        if (exists("droplist")){
          droplist <- (droplist)
        }
        # if the droplist doesn't exist, create it
        else {
          droplist <- (NA)
          rm(droplist)
        }
      }
    }
  }
  remnames <- names(splitX_df)
  if (exists("droplist")) {
    splitX_df  <- (splitX_df[,-(droplist)])
    splitX_df <- data.frame(splitX_df)
    colnames(splitX_df) <- remnames[-(droplist)]
  }
  else {
    splitX_df  <- splitX_df
  }
  #ifelse(exists("droplist"), (splitX_df  <- (splitX_df[,-(droplist)])), (splitX_df  <- splitX_df))
  return(list(splitX_df, split_data_df))
}

# Function to recursively partition dataset on best splits

MTPart <- function(X, Z, data, continuous = "quantile", quantseq = seq(0,1,0.25), wt=NULL, evalmethod = "avgIG", alpha = 0.05, IGcutoff = 0.95, depth=6,
                   nodesize=20, cp=0.02, reuse=FALSE, parallelpart=TRUE, parallelsplit=2, paralleldepth=2, splitmin=floor(nodesize/2)) { #and all inputs for MultiEval
  mtpart_splits <- split_df <- splitX <- splitZ <- vector(mode = "list", length = 2^(depth))
  i <- 1
  split_df[[i]] <- temp  <- data
  splitZ[[i]]   <- tempZ <- Z
  splitX[[i]]   <- tempX <- X
  root_eval     <- MTSummary(targets=splitZ[[i]], data=split_df[[i]])
  df <- data.frame(c(NA),c(NA))
  names(df) <- c("parent","child")
  mtpart_splits[[i]]$NodeID  <- paste(i)
  mtpart_splits[[i]]$SplitVar<- paste("Root")
  mtpart_splits[[i]]$Var     <- paste("Root")
  mtpart_splits[[i]]$Thresh  <- paste("Root")
  mtpart_splits[[i]]$N       <- paste(nrow(split_df[[i]]))
  mtpart_splits[[i]]$Pnode   <- paste(nrow(split_df[[i]])/nrow(split_df[[1]]))
  mtpart_splits[[i]]$Targets <- root_eval
  misclass_targets <- Xerr_targets <- Xstd_targets <- as.list(1:length(splitZ[[i]]$Z))
  for (j in 1:length(misclass_targets)) {
    if(splitZ[[i]]$Definitions[j]=="Cat") {
      mtpart_splits[[i]]$Targets[[j]]$relerr <- mtpart_splits[[i]]$Targets[[j]]$expectedloss/mtpart_splits[[1]]$Targets[[j]]$expectedloss
    }
    else if(splitZ[[i]]$Definitions[j] == "Surv") {
      mtpart_splits[[i]]$Targets[[j]]$relerr <- mtpart_splits[[i]]$Targets[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
    }
    else if(splitZ[[i]]$Definitions[j] == "Count") {
      mtpart_splits[[i]]$Targets[[j]]$relerr <- mtpart_splits[[i]]$Targets[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
    }
    else {
      mtpart_splits[[i]]$Targets[[j]]$relerr <- mtpart_splits[[i]]$Targets[[j]]$MSE/mtpart_splits[[1]]$Targets[[j]]$MSE
    }
    misclass_targets[[j]] <- mtpart_splits[[i]]$Targets[[j]]$relerr
  }
  ifelse(!is.null(wt), (mtpart_splits[[i]]$relerr <- weighted.mean(as.numeric(misclass_targets), w=(wt), na.rm=TRUE)),
         (mtpart_splits[[i]]$relerr <- mean(as.numeric(misclass_targets))))
  if (parallelpart==TRUE & !is.na(parallelsplit) & !is.na(paralleldepth)) {
    for (i in 1:2^(depth)) {
      # If the node i exists:
      if (!is.null(mtpart_splits[[i]]) ) {
        # And if the node i is sufficiently large (defined by nodesize argument):
        if (!is.null(data.frame(splitX[[i]])) & nrow(data.frame(splitX[[i]])) >= nodesize & ncol(data.frame(splitX[[i]])) > 0 ) {
          # Construct parallel trees of specified depth & select split var based on subtree relative error
          levlist <- vector(mode = "list", length = 0)
          for (o in 1:length(splitX[[i]])) {
            levlist <- append(levlist, levels(splitX[[i]][[o]]))
          }
          ifelse(parallelsplit=="all", parallelsplit <- length(levlist), parallelsplit <- parallelsplit)
          paralleltrees <- pareval <- vector(mode = "list", length = (parallelsplit))
          for (p in 1:length(paralleltrees)) {
            #Adjust to stop lookahead beyond tree depth?
            #ifelse(i+(2^paralleldepth)-1 <= 2^(depth), paralleldepth <- paralleldepth, paralleldepth <- 1)
            subtree <- subtree_df <- subtree_X <- subtree_Z <- vector(mode = "list", length = (2^(paralleldepth+1)-1))
            subtree[[1]] <- mtpart_splits[[i]]
            subtree_df[[1]] <- split_df[[i]]
            subtree_X[[1]]  <- splitX[[i]]
            subtree_Z[[1]]  <- splitZ[[i]]
            for (l in 1:length(subtree)) {
              # If the node i exists:
              if (!is.null(subtree[[l]]) ) {
                # And if the node i is sufficiently large (defined by nodesize argument):
                if (!is.null(data.frame(subtree_X[[l]])) & nrow(data.frame(subtree_X[[l]])) >= nodesize & ncol(data.frame(subtree_X[[l]])) > 0 ) {
                  ifelse(reuse==TRUE, parentsplit <- "skip", parentsplit <- subtree[[l]]$Var)
                  prep <- suppressWarnings(SplitPrep(Xdf=subtree_X[[l]], df=subtree_df[[l]], data_splt=subtree_df[[1]], parentsplit))
                  if (length(!is.na(data.frame(prep[[1]]))) >= 1) {
                    #>>>>>>>>>>>>>>>>>  prep giving unequal data in l=4 - problem with differing lengths of input data (64 vs. 78)
                    eval_temp <- NA
                    try(eval_temp <- suppressWarnings(MultiEval(X=data.frame(prep[[1]]), subtree_Z[[l]], data=prep[[2]], continuous = continuous, quantseq = quantseq, wt = wt, evalmethod = evalmethod, alpha = alpha, IGcutoff = IGcutoff, splitmin=splitmin)) , silent=TRUE)
                    # If the node i can be evaluated with the split variables and targets:
                    if (!is.na(eval_temp[2]) & (2*l+0 <= (2^(paralleldepth+1)-1)) & (2*l+1 <= (2^(paralleldepth+1)-1)) ) {
                      splitdf   <- eval_temp[[2]] #Extract splitvar with top rank
                      splitdf   <- (splitdf[!duplicated(splitdf[,c(1,3:ncol(splitdf))]), c(1:ncol(splitdf))])
                      temp      <- subtree_df[[l]]
                      splitdf   <- splitdf[order(splitdf$Rank),]
                      #splitvar   <- splitdf[p,]$Split
                      splitvar  <- as.character(head(splitdf[p,]$Split, n=1))
                      var       <- as.character(head(splitdf[p,]$Xm, n=1))
                      varnum    <- which(colnames(temp)==var)
                      notation  <- (unlist(strsplit(splitvar, " ")))
                      notation  <- notation[2]
                      thresh    <- str_remove(splitvar, var)
                      ifelse(notation == "in", threshold <- str_remove(thresh, " in "),
                             ifelse(notation == "<", threshold <- str_remove(thresh, " < "), NA))
                      # Subset data based on selected split
                      splitL_Z <- splitR_Z <- subtree_Z[[l]]
                      ifelse(notation == "in", splitL <- (temp[which(temp[,c(varnum)] == threshold), c(1:ncol(temp))]),
                             ifelse(notation == "<", splitL  <- (temp[which(temp[,c(varnum)] < as.numeric(threshold)), c(1:ncol(temp))]), NA))
                      splitL_Z$Z <- subset(splitL_Z$Z, row.names(splitL_Z$Z) %in% row.names(splitL))
                      ifelse(notation == "in", splitR <- (temp[which(temp[,c(varnum)] != threshold), c(1:ncol(temp))]),
                             ifelse(notation == "<", splitR <- (temp[which(temp[,c(varnum)] >= as.numeric(threshold)), c(1:ncol(temp))]), NA))
                      splitR_Z$Z <- subset(splitR_Z$Z, row.names(splitR_Z$Z) %in% row.names(splitR))
                      ifelse(notation == "in", splitvarR <- paste(var, threshold, sep = " not in "),
                             ifelse(notation == "<", splitvarR <- paste(var, threshold, sep = " >= "), NA))
                      # Evaluate child nodes across targets using MTSummary
                      splitL_eval <- suppressWarnings(MTSummary(splitL_Z, data=splitL))
                      splitR_eval <- suppressWarnings(MTSummary(splitR_Z, data=splitR))
                      # Evaluate split using CV error & sd (caret) --> Record for parent node
                      subtree[[l]]$PartVar <- var
                      misclass_targets_L <- misclass_targets_R <- as.list(1:length(subtree_Z[[2*l+0]]$Z))
                      #if ((l %% 2) == 0) {pnid <- (l/2)}
                      #else {pnid <- ((l-1)/2)}
                      for (j in 1:length(splitL_eval)) {
                        if(subtree_Z[[l]]$Definitions[j]=="Cat") {
                          splitL_eval[[j]]$relerr <- splitL_eval[[j]]$expectedloss/subtree[[1]]$Targets[[j]]$expectedloss
                        }
                        else if(subtree_Z[[l]]$Definitions[j] == "Surv") {
                          splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/subtree[[1]]$Targets[[j]]$deviance
                        }
                        else if(subtree_Z[[l]]$Definitions[j] == "Count") {
                          splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/subtree[[1]]$Targets[[j]]$deviance
                        }
                        else {
                          splitL_eval[[j]]$relerr <- splitL_eval[[j]]$MSE/subtree[[1]]$Targets[[j]]$MSE
                        }
                        misclass_targets_L[[j]] <- splitL_eval[[j]]$relerr
                      }
                      ifelse(!is.null(wt), (L_relerr <- weighted.mean(as.numeric(misclass_targets_L), w=(wt), na.rm=TRUE)),
                             (L_relerr <- mean(as.numeric(misclass_targets_L), na.rm = TRUE)))
                      
                      for (j in 1:length(splitR_eval)) {
                        if(subtree_Z[[l]]$Definitions[j]=="Cat") {
                          splitR_eval[[j]]$relerr <- splitR_eval[[j]]$expectedloss/subtree[[1]]$Targets[[j]]$expectedloss
                        }
                        else if(subtree_Z[[l]]$Definitions[j] == "Surv") {
                          splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/subtree[[1]]$Targets[[j]]$deviance
                        }
                        else if(subtree_Z[[l]]$Definitions[j] == "Count") {
                          splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/subtree[[1]]$Targets[[j]]$deviance
                        }
                        else {
                          splitR_eval[[j]]$relerr <- splitR_eval[[j]]$MSE/subtree[[1]]$Targets[[j]]$MSE
                        }
                        misclass_targets_R[[j]] <- splitR_eval[[j]]$relerr
                      }
                      ifelse(!is.null(wt), (R_relerr <- weighted.mean(as.numeric(misclass_targets_R), w=(wt), na.rm=TRUE)),
                             (R_relerr <- mean(as.numeric(misclass_targets_R), na.rm = TRUE)))
                      
                      subtree[[l]]$CP      <- (subtree[[l]]$relerr - ((L_relerr + R_relerr)/2))
                      
                      subtree[[l]]$Eval <- splitdf
                      #if (subtree[[l]]$CP >= cp) {
                      if (!is.na(subtree[[l]]$CP)) {
                        # Record child data frames, features, and targets
                        subtree_df[[2*l+0]] <- splitL
                        subtree_df[[2*l+1]] <- splitR
                        subtree_Z[[2*l+0]] <- splitL_Z
                        subtree_Z[[2*l+1]] <- splitR_Z
                        subtree_X[[2*l+0]] <- subset(subtree_X[[l]], row.names(subtree_X[[l]]) %in% row.names(splitL))
                        subtree_X[[2*l+1]] <- subset(subtree_X[[l]], row.names(subtree_X[[l]]) %in% row.names(splitR))
                        # Record left-child node
                        subtree[[2*l+0]]$NodeID  <- paste(2*l+0)
                        subtree[[2*l+0]]$SplitVar<- paste(splitvar)
                        subtree[[2*l+0]]$Var     <- paste(var)
                        subtree[[2*l+0]]$Thresh  <- paste(threshold)
                        subtree[[2*l+0]]$N       <- paste(nrow(subtree_df[[2*l+0]]))
                        subtree[[2*l+0]]$Pnode   <- paste(nrow(subtree_df[[2*l+0]])/nrow(subtree_df[[1]]))
                        subtree[[2*l+0]]$Targets <- splitL_eval
                        Xerr_targets <- Xstd_targets <- as.list(1:length(subtree_Z[[2*l+0]]$Z))
                        for (j in 1:length(misclass_targets)) {
                          Xerr_targets[[j]]     <- subtree[[2*l+0]]$Targets[[j]]$Xerror
                          Xstd_targets[[j]]     <- subtree[[2*l+0]]$Targets[[j]]$Xstd
                        }
                        subtree[[2*l+0]]$relerr <- L_relerr
                        # Record right-child node
                        subtree[[2*l+1]]$NodeID  <- paste(2*l+1)
                        subtree[[2*l+1]]$SplitVar<- paste(splitvarR)
                        subtree[[2*l+1]]$Var     <- paste(var)
                        subtree[[2*l+1]]$Thresh  <- paste(threshold)
                        subtree[[2*l+1]]$N       <- paste(nrow(subtree_df[[2*l+1]]))
                        subtree[[2*l+1]]$Pnode   <- paste(nrow(subtree_df[[2*l+1]])/nrow(subtree_df[[1]]))
                        subtree[[2*l+1]]$Targets <- splitR_eval
                        Xerr_targets <- Xstd_targets <- as.list(1:length(subtree_Z[[2*l+1]]$Z))
                        for (j in 1:length(misclass_targets)) {
                          Xerr_targets[[j]] <- subtree[[2*l+1]]$Targets[[j]]$Xerror
                          Xstd_targets[[j]] <- subtree[[2*l+1]]$Targets[[j]]$Xstd
                        }
                        subtree[[2*l+1]]$relerr <- R_relerr
                      }
                      else {
                        subtree[[l]]$NodeID  <- paste(subtree[[l]]$NodeID, "*")
                        #subtree[[l]]$SXerror <- NA
                        #subtree[[l]]$SXstd   <- NA
                        subtree[[l]]$CP      <- NA
                      }
                    }
                    # If the node i cannot be evaluated, label node i as terminal (*) and move to next node:
                    else {
                      subtree[[l]]$NodeID  <- paste(subtree[[l]]$NodeID, "*")
                      #subtree[[l]]$SXerror <- NA
                      #subtree[[l]]$SXstd   <- NA
                      subtree[[l]]$CP      <- NA
                    }
                  }
                  # Move on to next node: update i
                  l <- l + 1
                }
                # If node i is too small to partition (defined by nodesize), label node i as terminal (*) and move to next node:
                else {
                  subtree[[l]]$NodeID <- paste(subtree[[l]]$NodeID, "*")
                  #subtree[[l]]$SXerror <- NA
                  #subtree[[l]]$SXstd   <- NA
                  subtree[[l]]$CP      <- NA
                  l <- l + 1
                }
              }
              # If node i doesn't exist, move on to next node:
              else {
                l <- l + 1
              }
            }
            paralleltrees[[p]] <- subtree
          }
          for (r in 1:length(pareval)) {
            relerrs <- vector(mode = "list", length = (2^(paralleldepth+1)-1))
            for (l in 1:length(relerrs)) {
              if (!is.null(paralleltrees[[r]][[l]])) {
                nodeid    <- (unlist(strsplit(paralleltrees[[r]][[l]]$NodeID, " ")))
                if (length(nodeid)>=2) {
                  nodeN     <- paralleltrees[[r]][[l]]$N
                  rootN     <- paralleltrees[[r]][[1]]$N
                  relerrs[[l]] <- paralleltrees[[r]][[l]]$relerr * (as.numeric(nodeN)/as.numeric(rootN))
                }
                else {
                  relerrs[[l]] <- NA
                }
              }
              else {
                relerrs[[l]] <- NA
              }
            }
            pareval[[r]] <- mean(as.numeric(unlist(relerrs)), na.rm = TRUE)
          }
          beststid  <- grep(min(as.numeric(unlist(pareval))), pareval)[1]
          bestst    <- paralleltrees[[beststid]]
          ifelse(!is.null(bestst[[2]]), splitvar  <- as.character(bestst[[2]]$SplitVar), splitvar <- NA)
          # If the node i can be evaluated with the split variables and targets:
          if (!is.na(splitvar) & (2*i+0 <= 2^(depth)) & (2*i+1 <= 2^(depth)) ) {
            #splitdf   <- eval_temp[[2]] #Extract splitvar with top rank
            temp      <- split_df[[i]]
            #splitvar  <- as.character(head(splitdf$Split[splitdf$Rank == min(splitdf$Rank)], n=1))
            #var       <- as.character(head(splitdf$Xm[splitdf$Rank == min(splitdf$Rank)], n=1))
            notation  <- (unlist(strsplit(splitvar, " ")))
            var       <- notation[1]
            varnum    <- which(colnames(temp)==var)
            notation  <- notation[2]
            thresh    <- str_remove(splitvar, var)
            ifelse(notation == "in", threshold <- str_remove(thresh, " in "),
                   ifelse(notation == "<", threshold <- str_remove(thresh, " < "), NA))
            # Subset data based on selected split
            splitL_Z <- splitR_Z <- splitZ[[i]]
            ifelse(notation == "in", splitL <- (temp[which(temp[,c(varnum)] == threshold), c(1:ncol(temp))]),
                   ifelse(notation == "<", splitL  <- (temp[which(temp[,c(varnum)] < as.numeric(threshold)), c(1:ncol(temp))]), NA))
            splitL_Z$Z <- subset(splitL_Z$Z, row.names(splitL_Z$Z) %in% row.names(splitL))
            ifelse(notation == "in", splitR <- (temp[which(temp[,c(varnum)] != threshold), c(1:ncol(temp))]),
                   ifelse(notation == "<", splitR <- (temp[which(temp[,c(varnum)] >= as.numeric(threshold)), c(1:ncol(temp))]), NA))
            splitR_Z$Z <- subset(splitR_Z$Z, row.names(splitR_Z$Z) %in% row.names(splitR))
            ifelse(notation == "in", splitvarR <- paste(var, threshold, sep = " not in "),
                   ifelse(notation == "<", splitvarR <- paste(var, threshold, sep = " >= "), NA))
            # Evaluate child nodes across targets using MTSummary
            splitL_eval <- suppressWarnings(MTSummary(splitL_Z, data=splitL))
            splitR_eval <- suppressWarnings(MTSummary(splitR_Z, data=splitR))
            # Evaluate split using CV error & sd (caret) --> Record for parent node
            mtpart_splits[[i]]$PartVar <- var
            misclass_targets_L <- misclass_targets_R <- as.list(1:length(splitZ[[2*i+0]]$Z))
            
            for (j in 1:length(splitL_eval)) {
              if(splitZ[[i]]$Definitions[j]=="Cat") {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$expectedloss/mtpart_splits[[1]]$Targets[[j]]$expectedloss
              }
              else if(splitZ[[i]]$Definitions[j] == "Surv") {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else if(splitZ[[i]]$Definitions[j] == "Count") {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$MSE/mtpart_splits[[1]]$Targets[[j]]$MSE
              }
              misclass_targets_L[[j]] <- splitL_eval[[j]]$relerr
            }
            ifelse(!is.null(wt), (L_relerr <- weighted.mean(as.numeric(misclass_targets_L), w=(wt), na.rm=TRUE)),
                   (L_relerr <- mean(as.numeric(misclass_targets_L), na.rm = TRUE)))
            
            for (j in 1:length(splitR_eval)) {
              if(splitZ[[i]]$Definitions[j]=="Cat") {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$expectedloss/mtpart_splits[[1]]$Targets[[j]]$expectedloss
              }
              else if(splitZ[[i]]$Definitions[j] == "Surv") {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else if(splitZ[[i]]$Definitions[j] == "Count") {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$MSE/mtpart_splits[[1]]$Targets[[j]]$MSE
              }
              misclass_targets_R[[j]] <- splitR_eval[[j]]$relerr
            }
            ifelse(!is.null(wt), (R_relerr <- weighted.mean(as.numeric(misclass_targets_R), w=(wt), na.rm=TRUE)),
                   (R_relerr <- mean(as.numeric(misclass_targets_R), na.rm = TRUE)))
            
            mtpart_splits[[i]]$CP      <- mtpart_splits[[i]]$relerr - ((L_relerr + R_relerr)/2)
            # Evaluate split using CV error & sd (caret) --> Record for parent node
            splitCVeval <- CVsplitEval(splitvar, splitX[[i]], splitZ[[i]], split_df[[i]])
            mtpart_splits[[i]]$CVeval <- splitCVeval
            CVeval_Xerr_targets <- CVeval_Xstd_targets <- as.list(1:length(splitZ[[i]]$Z))
            for (j in 1:length(splitZ[[i]]$Z)) {
              if(splitZ[[i]]$Definitions[j]=="Cat") {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Accuracy)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$AccuracySD
              }
              else if(splitZ[[i]]$Definitions[j] == "Surv") {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Rsquared)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$RsquaredSD
              }
              else if(splitZ[[i]]$Definitions[j] == "Count") {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Rsquared)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$RsquaredSD
              }
              else {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Rsquared)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$RsquaredSD
              }
              CVeval_Xerr_targets[[j]] <- mtpart_splits[[i]]$CVeval[[j]]$Xerror
              CVeval_Xstd_targets[[j]] <- mtpart_splits[[i]]$CVeval[[j]]$Xstd
            }
            ifelse(!is.null(wt), (mtpart_splits[[i]]$SXerror <- (weighted.mean(as.numeric(CVeval_Xerr_targets), w=(wt), na.rm=TRUE))),
                   (mtpart_splits[[i]]$SXerror <- (mean(as.numeric(CVeval_Xerr_targets), na.rm=TRUE))))
            ifelse(!is.null(wt), (mtpart_splits[[i]]$SXstd <- ( weighted.mean(as.numeric(CVeval_Xstd_targets), w=(wt), na.rm=TRUE))),
                   (mtpart_splits[[i]]$SXstd <- ( mean(as.numeric(CVeval_Xstd_targets), na.rm=TRUE))))
            mtpart_splits[[i]]$Eval <- splitdf
            if (mtpart_splits[[i]]$CP >= cp) {
              # Record child data frames, features, and targets
              split_df[[2*i+0]] <- splitL
              split_df[[2*i+1]] <- splitR
              splitZ[[2*i+0]] <- splitL_Z
              splitZ[[2*i+1]] <- splitR_Z
              splitX[[2*i+0]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitL))
              splitX[[2*i+1]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitR))
              # Record left-child node
              mtpart_splits[[2*i+0]]$NodeID  <- paste(2*i+0)
              mtpart_splits[[2*i+0]]$SplitVar<- paste(splitvar)
              mtpart_splits[[2*i+0]]$Var     <- paste(var)
              mtpart_splits[[2*i+0]]$Thresh  <- paste(threshold)
              mtpart_splits[[2*i+0]]$N       <- paste(nrow(split_df[[2*i+0]]))
              mtpart_splits[[2*i+0]]$Pnode   <- paste(nrow(split_df[[2*i+0]])/nrow(split_df[[1]]))
              mtpart_splits[[2*i+0]]$Targets <- splitL_eval
              Xerr_targets <- Xstd_targets <- as.list(1:length(splitZ[[2*i+0]]$Z))
              for (j in 1:length(misclass_targets)) {
                Xerr_targets[[j]]     <- mtpart_splits[[2*i+0]]$Targets[[j]]$Xerror
                Xstd_targets[[j]]     <- mtpart_splits[[2*i+0]]$Targets[[j]]$Xstd
              }
              mtpart_splits[[2*i+0]]$relerr <- L_relerr
              # Record right-child node
              mtpart_splits[[2*i+1]]$NodeID  <- paste(2*i+1)
              mtpart_splits[[2*i+1]]$SplitVar<- paste(splitvarR)
              mtpart_splits[[2*i+1]]$Var     <- paste(var)
              mtpart_splits[[2*i+1]]$Thresh  <- paste(threshold)
              mtpart_splits[[2*i+1]]$N       <- paste(nrow(split_df[[2*i+1]]))
              mtpart_splits[[2*i+1]]$Pnode   <- paste(nrow(split_df[[2*i+1]])/nrow(split_df[[1]]))
              mtpart_splits[[2*i+1]]$Targets <- splitR_eval
              Xerr_targets <- Xstd_targets <- as.list(1:length(splitZ[[2*i+1]]$Z))
              for (j in 1:length(misclass_targets)) {
                Xerr_targets[[j]] <- mtpart_splits[[2*i+1]]$Targets[[j]]$Xerror
                Xstd_targets[[j]] <- mtpart_splits[[2*i+1]]$Targets[[j]]$Xstd
              }
              mtpart_splits[[2*i+1]]$relerr <- R_relerr
              # Record parent node id in child node id slots
              df[i,]$child         <- mtpart_splits[[i]]$NodeID
              df[(2*i+0),]$parent  <- mtpart_splits[[i]]$NodeID
              df[(2*i+1),]$parent  <- mtpart_splits[[i]]$NodeID
            }
            else {
              mtpart_splits[[i]]$NodeID  <- paste(mtpart_splits[[i]]$NodeID, "*")
              mtpart_splits[[i]]$SXerror <- NA
              mtpart_splits[[i]]$SXstd   <- NA
              mtpart_splits[[i]]$CP      <- NA
              df[i,]$child         <- mtpart_splits[[i]]$NodeID
            }
          }
          # If the node i cannot be evaluated, label node i as terminal (*) and move to next node:
          else {
            mtpart_splits[[i]]$NodeID  <- paste(mtpart_splits[[i]]$NodeID, "*")
            mtpart_splits[[i]]$SXerror <- NA
            mtpart_splits[[i]]$SXstd   <- NA
            mtpart_splits[[i]]$CP      <- NA
            
            df[i,]$child         <- mtpart_splits[[i]]$NodeID
          }
          # Move on to next node: update i
          i <- i + 1
        }
        # If node i is too small to partition (defined by nodesize), label node i as terminal (*) and move to next node:
        else {
          mtpart_splits[[i]]$NodeID <- paste(mtpart_splits[[i]]$NodeID, "*")
          mtpart_splits[[i]]$SXerror <- NA
          mtpart_splits[[i]]$SXstd   <- NA
          mtpart_splits[[i]]$CP      <- NA
          
          df[i,]$child         <- mtpart_splits[[i]]$NodeID
          i <- i + 1
        }
      }
      # If node i doesn't exist, move on to next node:
      else {
        i <- i + 1
      }
    }
  }
  else {
    for (i in 1:2^(depth)) {
      # If the node i exists:
      if (!is.null(mtpart_splits[[i]]) ) {
        # And if the node i is sufficiently large (defined by nodesize argument):
        if (!is.null(data.frame(splitX[[i]])) & nrow(data.frame(splitX[[i]])) >= nodesize & ncol(data.frame(splitX[[i]])) > 0 ) {
          ifelse(reuse==TRUE, parentsplit <- "skip", parentsplit <- mtpart_splits[[i]]$Var)
          prep <- suppressWarnings(SplitPrep(Xdf=splitX[[i]], df=split_df[[i]], data_splt=split_df[[1]], parentsplit))
          eval_temp <- NA
          try(eval_temp <- suppressWarnings(MultiEval(X=data.frame(prep[[1]]), splitZ[[i]], data=prep[[2]], continuous = continuous, quantseq = quantseq, wt = wt, evalmethod = evalmethod, alpha = alpha, IGcutoff = IGcutoff, splitmin = splitmin)), silent=TRUE )
          # If the node i can be evaluated with the split variables and targets:
          if (!is.na(eval_temp[2]) & (2*i+0 <= 2^(depth)) & (2*i+1 <= 2^(depth)) ) {
            splitdf   <- eval_temp[[2]] #Extract splitvar with top rank
            temp      <- split_df[[i]]
            splitvar  <- as.character(head(splitdf$Split[splitdf$Rank == min(splitdf$Rank)], n=1))
            var       <- as.character(head(splitdf$Xm[splitdf$Rank == min(splitdf$Rank)], n=1))
            varnum    <- which(colnames(temp)==var)
            notation  <- (unlist(strsplit(splitvar, " ")))
            notation  <- notation[2]
            thresh    <- str_remove(splitvar, var)
            ifelse(notation == "in", threshold <- str_remove(thresh, " in "),
                   ifelse(notation == "<", threshold <- str_remove(thresh, " < "), NA))
            # Subset data based on selected split
            splitL_Z <- splitR_Z <- splitZ[[i]]
            ifelse(notation == "in", splitL <- (temp[which(temp[,c(varnum)] == threshold), c(1:ncol(temp))]),
                   ifelse(notation == "<", splitL  <- (temp[which(temp[,c(varnum)] < as.numeric(threshold)), c(1:ncol(temp))]), NA))
            splitL_Z$Z <- subset(splitL_Z$Z, row.names(splitL_Z$Z) %in% row.names(splitL))
            ifelse(notation == "in", splitR <- (temp[which(temp[,c(varnum)] != threshold), c(1:ncol(temp))]),
                   ifelse(notation == "<", splitR <- (temp[which(temp[,c(varnum)] >= as.numeric(threshold)), c(1:ncol(temp))]), NA))
            splitR_Z$Z <- subset(splitR_Z$Z, row.names(splitR_Z$Z) %in% row.names(splitR))
            ifelse(notation == "in", splitvarR <- paste(var, threshold, sep = " not in "),
                   ifelse(notation == "<", splitvarR <- paste(var, threshold, sep = " >= "), NA))
            # Evaluate child nodes across targets using MTSummary
            splitL_eval <- suppressWarnings(MTSummary(splitL_Z, data=splitL))
            splitR_eval <- suppressWarnings(MTSummary(splitR_Z, data=splitR))
            # Evaluate split using CV error & sd (caret) --> Record for parent node
            mtpart_splits[[i]]$PartVar <- var
            misclass_targets_L <- misclass_targets_R <- as.list(1:length(splitZ[[2*i+0]]$Z))
            
            for (j in 1:length(splitL_eval)) {
              if(splitZ[[i]]$Definitions[j]=="Cat") {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$expectedloss/mtpart_splits[[1]]$Targets[[j]]$expectedloss
              }
              else if(splitZ[[i]]$Definitions[j] == "Surv") {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else if(splitZ[[i]]$Definitions[j] == "Count") {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else {
                splitL_eval[[j]]$relerr <- splitL_eval[[j]]$MSE/mtpart_splits[[1]]$Targets[[j]]$MSE
              }
              misclass_targets_L[[j]] <- splitL_eval[[j]]$relerr
            }
            ifelse(!is.null(wt), (L_relerr <- weighted.mean(as.numeric(misclass_targets_L), w=(wt), na.rm=TRUE)),
                   (L_relerr <- mean(as.numeric(misclass_targets_L), na.rm = TRUE)))
            
            for (j in 1:length(splitR_eval)) {
              if(splitZ[[i]]$Definitions[j]=="Cat") {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$expectedloss/mtpart_splits[[1]]$Targets[[j]]$expectedloss
              }
              else if(splitZ[[i]]$Definitions[j] == "Surv") {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else if(splitZ[[i]]$Definitions[j] == "Count") {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits[[1]]$Targets[[j]]$deviance
              }
              else {
                splitR_eval[[j]]$relerr <- splitR_eval[[j]]$MSE/mtpart_splits[[1]]$Targets[[j]]$MSE
              }
              misclass_targets_R[[j]] <- splitR_eval[[j]]$relerr
            }
            ifelse(!is.null(wt), (R_relerr <- weighted.mean(as.numeric(misclass_targets_R), w=(wt), na.rm=TRUE)),
                   (R_relerr <- mean(as.numeric(misclass_targets_R), na.rm = TRUE)))
            
            mtpart_splits[[i]]$CP      <- mtpart_splits[[i]]$relerr - ((L_relerr + R_relerr)/2)
            # Evaluate split using CV error & sd (caret) --> Record for parent node
            #start <- Sys.time()
            #if (droplevels(split_df[[i]][,varnum])) {}
            splitCVeval <- CVsplitEval(splitvar, splitX[[i]], splitZ[[i]], split_df[[i]])
            #end <- Sys.time()
            #difftime(end, start)
            mtpart_splits[[i]]$CVeval <- splitCVeval
            CVeval_Xerr_targets <- CVeval_Xstd_targets <- as.list(1:length(splitZ[[i]]$Z))
            for (j in 1:length(splitZ[[i]]$Z)) {
              if(splitZ[[i]]$Definitions[j]=="Cat") {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Accuracy)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$AccuracySD
              }
              else if(splitZ[[i]]$Definitions[j] == "Surv") {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Rsquared)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$RsquaredSD
              }
              else if(splitZ[[i]]$Definitions[j] == "Count") {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Rsquared)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$RsquaredSD
              }
              else {
                mtpart_splits[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits[[i]]$CVeval[[j]]$Rsquared)
                mtpart_splits[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits[[i]]$CVeval[[j]]$RsquaredSD
              }
              CVeval_Xerr_targets[[j]] <- mtpart_splits[[i]]$CVeval[[j]]$Xerror
              CVeval_Xstd_targets[[j]] <- mtpart_splits[[i]]$CVeval[[j]]$Xstd
            }
            ifelse(!is.null(wt), (mtpart_splits[[i]]$SXerror <- (weighted.mean(as.numeric(CVeval_Xerr_targets), w=(wt), na.rm=TRUE))),
                   (mtpart_splits[[i]]$SXerror <- (mean(as.numeric(CVeval_Xerr_targets)))))
            ifelse(!is.null(wt), (mtpart_splits[[i]]$SXstd <- ( weighted.mean(as.numeric(CVeval_Xstd_targets), w=(wt), na.rm=TRUE))),
                   (mtpart_splits[[i]]$SXstd <- ( mean(as.numeric(CVeval_Xstd_targets)))))
            mtpart_splits[[i]]$Eval <- splitdf
            if (mtpart_splits[[i]]$CP >= cp) {
              # Record child data frames, features, and targets
              split_df[[2*i+0]] <- splitL
              split_df[[2*i+1]] <- splitR
              splitZ[[2*i+0]] <- splitL_Z
              splitZ[[2*i+1]] <- splitR_Z
              splitX[[2*i+0]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitL))
              splitX[[2*i+1]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitR))
              # Record left-child node
              mtpart_splits[[2*i+0]]$NodeID  <- paste(2*i+0)
              mtpart_splits[[2*i+0]]$SplitVar<- paste(splitvar)
              mtpart_splits[[2*i+0]]$Var     <- paste(var)
              mtpart_splits[[2*i+0]]$Thresh  <- paste(threshold)
              mtpart_splits[[2*i+0]]$N       <- paste(nrow(split_df[[2*i+0]]))
              mtpart_splits[[2*i+0]]$Pnode   <- paste(nrow(split_df[[2*i+0]])/nrow(split_df[[1]]))
              mtpart_splits[[2*i+0]]$Targets <- splitL_eval
              Xerr_targets <- Xstd_targets <- as.list(1:length(splitZ[[2*i+0]]$Z))
              for (j in 1:length(misclass_targets)) {
                Xerr_targets[[j]]     <- mtpart_splits[[2*i+0]]$Targets[[j]]$Xerror
                Xstd_targets[[j]]     <- mtpart_splits[[2*i+0]]$Targets[[j]]$Xstd
              }
              mtpart_splits[[2*i+0]]$relerr <- L_relerr
              # Record right-child node
              mtpart_splits[[2*i+1]]$NodeID  <- paste(2*i+1)
              mtpart_splits[[2*i+1]]$SplitVar<- paste(splitvarR)
              mtpart_splits[[2*i+1]]$Var     <- paste(var)
              mtpart_splits[[2*i+1]]$Thresh  <- paste(threshold)
              mtpart_splits[[2*i+1]]$N       <- paste(nrow(split_df[[2*i+1]]))
              mtpart_splits[[2*i+1]]$Pnode   <- paste(nrow(split_df[[2*i+1]])/nrow(split_df[[1]]))
              mtpart_splits[[2*i+1]]$Targets <- splitR_eval
              Xerr_targets <- Xstd_targets <- as.list(1:length(splitZ[[2*i+1]]$Z))
              for (j in 1:length(misclass_targets)) {
                Xerr_targets[[j]] <- mtpart_splits[[2*i+1]]$Targets[[j]]$Xerror
                Xstd_targets[[j]] <- mtpart_splits[[2*i+1]]$Targets[[j]]$Xstd
              }
              mtpart_splits[[2*i+1]]$relerr <- R_relerr
              # Record parent node id in child node id slots
              df[i,]$child         <- mtpart_splits[[i]]$NodeID
              df[(2*i+0),]$parent  <- mtpart_splits[[i]]$NodeID
              df[(2*i+1),]$parent  <- mtpart_splits[[i]]$NodeID
            }
            else {
              mtpart_splits[[i]]$NodeID  <- paste(mtpart_splits[[i]]$NodeID, "*")
              mtpart_splits[[i]]$SXerror <- NA
              mtpart_splits[[i]]$SXstd   <- NA
              mtpart_splits[[i]]$CP      <- NA
              
              df[i,]$child         <- mtpart_splits[[i]]$NodeID
            }
          }
          # If the node i cannot be evaluated, label node i as terminal (*) and move to next node:
          else {
            mtpart_splits[[i]]$NodeID  <- paste(mtpart_splits[[i]]$NodeID, "*")
            mtpart_splits[[i]]$SXerror <- NA
            mtpart_splits[[i]]$SXstd   <- NA
            mtpart_splits[[i]]$CP      <- NA
            
            df[i,]$child         <- mtpart_splits[[i]]$NodeID
          }
          # Move on to next node: update i
          i <- i + 1
        }
        # If node i is too small to partition (defined by nodesize), label node i as terminal (*) and move to next node:
        else {
          mtpart_splits[[i]]$NodeID <- paste(mtpart_splits[[i]]$NodeID, "*")
          mtpart_splits[[i]]$SXerror <- NA
          mtpart_splits[[i]]$SXstd   <- NA
          mtpart_splits[[i]]$CP      <- NA
          
          df[i,]$child         <- mtpart_splits[[i]]$NodeID
          i <- i + 1
        }
      }
      # If node i doesn't exist, move on to next node:
      else {
        i <- i + 1
      }
    }
  }
  return(list(df, mtpart_splits)) #consider outputting eval directly instead of raw datasets
}


# Function to extract decision tree rules & apply them to test data

MTTest <- function(tree, X_test, Z_test, data_test, wt=NULL) {
  # Import trained tree
  df <- tree[[1]]
  mtpart_splits <- (tree[[2]])
  # Generate test tree
  mtpart_splits_test <- mtpart_splits
  i <- 1
  split_df <- splitX <- splitZ <- vector(mode = "list", length = length(mtpart_splits_test))
  split_df[[i]] <- temp  <- data_test
  splitZ[[i]]   <- tempZ <- Z_test
  splitX[[i]]   <- tempX <- X_test
  for (i in 1:length(mtpart_splits_test)) {
    if (i==1 & nrow(df) > 1 & !is.null(mtpart_splits_test[[i]])) {
      root_eval <- MTSummary(targets=Z_test, data=data_test)
      mtpart_splits_test[[i]]$N       <- paste(nrow(data_test))
      mtpart_splits_test[[i]]$Pnode   <- paste(nrow(data_test)/nrow(data_test))
      mtpart_splits_test[[i]]$Targets <- root_eval
      temp      <- split_df[[i]]
      splitvar  <- mtpart_splits[[2*i]]$SplitVar
      var       <- (unlist(strsplit(splitvar, " ")))[1]
      varnum    <- which(colnames(temp)==var)
      notation  <- (unlist(strsplit(splitvar, " ")))[2]
      thresh    <- (unlist(strsplit(splitvar, " ")))[3]
      ifelse(notation == "in", threshold <- str_remove(thresh, " in "),
             ifelse(notation == "<", threshold <- str_remove(thresh, " < "), NA))
      # Subset data based on selected split
      splitL_Z <- splitR_Z <- splitZ[[i]]
      ifelse(notation == "in", splitL <- (temp[which(temp[,c(varnum)] == threshold), c(1:ncol(temp))]),
             ifelse(notation == "<", splitL  <- (temp[which(temp[,c(varnum)] < as.numeric(threshold)), c(1:ncol(temp))]), NA))
      splitL_Z$Z <- subset(splitL_Z$Z, row.names(splitL_Z$Z) %in% row.names(splitL))
      ifelse(notation == "in", splitR <- (temp[which(temp[,c(varnum)] != threshold), c(1:ncol(temp))]),
             ifelse(notation == "<", splitR <- (temp[which(temp[,c(varnum)] >= as.numeric(threshold)), c(1:ncol(temp))]), NA))
      splitR_Z$Z <- subset(splitR_Z$Z, row.names(splitR_Z$Z) %in% row.names(splitR))
      ifelse(notation == "in", splitvarR <- paste(var, threshold, sep = " not in "),
             ifelse(notation == "<", splitvarR <- paste(var, threshold, sep = " >= "), NA))
      if (!is.null(nrow(splitL_Z)) & !is.null(nrow(splitR_Z))) {
        # Evaluate child nodes across targets using MTSummary
        splitL_eval <- suppressWarnings(MTSummary(splitL_Z, data=splitL))
        splitR_eval <- suppressWarnings(MTSummary(splitR_Z, data=splitR))
        # Evaluate split using CV error & sd (caret) --> Record for parent node
        misclass_targets_L <- misclass_targets_R <- as.list(1:length(splitZ[[i]]$Z))
        for (j in 1:length(splitL_eval)) {
          if(splitZ[[i]]$Definitions[j]=="Cat") {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$expectedloss/mtpart_splits_test[[1]]$Targets[[j]]$expectedloss
          }
          else if(splitZ[[i]]$Definitions[j] == "Surv") {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else if(splitZ[[i]]$Definitions[j] == "Count") {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$MSE/mtpart_splits_test[[1]]$Targets[[j]]$MSE
          }
          misclass_targets_L[[j]] <- splitL_eval[[j]]$relerr
        }
        ifelse(!is.null(wt), (L_relerr <- weighted.mean(as.numeric(misclass_targets_L), w=(wt), na.rm=TRUE)),
               (L_relerr <- mean(as.numeric(misclass_targets_L), na.rm = TRUE)))
        for (j in 1:length(splitR_eval)) {
          if(splitZ[[i]]$Definitions[j]=="Cat") {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$expectedloss/mtpart_splits_test[[1]]$Targets[[j]]$expectedloss
          }
          else if(splitZ[[i]]$Definitions[j] == "Surv") {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else if(splitZ[[i]]$Definitions[j] == "Count") {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$MSE/mtpart_splits_test[[1]]$Targets[[j]]$MSE
          }
          misclass_targets_R[[j]] <- splitR_eval[[j]]$relerr
        }
        ifelse(!is.null(wt), (R_relerr <- weighted.mean(as.numeric(misclass_targets_R), w=(wt), na.rm=TRUE)),
               (R_relerr <- mean(as.numeric(misclass_targets_R), na.rm = TRUE)))
        mtpart_splits_test[[i]]$CP      <- mtpart_splits_test[[i]]$relerr - ((L_relerr + R_relerr)/2)
        mtpart_splits_test[[i]]$CVeval <- CVsplitEval(mtpart_splits[[2*i]]$SplitVar, X_test, Z_test, data_test)
        CVeval_Xerr_targets <- CVeval_Xstd_targets <- as.list(1:length(Z_test$Z))
        for (j in 1:length(Z_test$Z)) {
          if(Z_test$Definitions[j]=="Cat") {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Accuracy)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$AccuracySD
          }
          else if(Z_test$Definitions[j] == "Surv") {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Rsquared)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$RsquaredSD
          }
          else if(Z_test$Definitions[j] == "Count") {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Rsquared)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$RsquaredSD
          }
          else {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Rsquared)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$RsquaredSD
          }
          CVeval_Xerr_targets[[j]] <- mtpart_splits_test[[i]]$CVeval[[j]]$Xerror
          CVeval_Xstd_targets[[j]] <- mtpart_splits_test[[i]]$CVeval[[j]]$Xstd
        }
        ifelse(!is.null(wt), (mtpart_splits_test[[i]]$SXerror <- (weighted.mean(as.numeric(CVeval_Xerr_targets), w=(wt), na.rm=TRUE))),
               (mtpart_splits_test[[i]]$SXerror <- (mean(as.numeric(CVeval_Xerr_targets)))))
        ifelse(!is.null(wt), (mtpart_splits_test[[i]]$SXstd <- ( weighted.mean(as.numeric(CVeval_Xstd_targets), w=(wt), na.rm=TRUE))),
               (mtpart_splits_test[[i]]$SXstd <- ( mean(as.numeric(CVeval_Xstd_targets)))))
        mtpart_splits_test[[i]]$Eval <- NA
        # Record child dataframes
        split_df[[2*i+0]] <- splitL
        split_df[[2*i+1]] <- splitR
        splitZ[[2*i+0]] <- splitL_Z
        splitZ[[2*i+1]] <- splitR_Z
        splitX[[2*i+0]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitL))
        splitX[[2*i+1]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitR))
        # Record left-child node
        mtpart_splits_test[[2*i+0]]$N       <- paste(nrow(split_df[[2*i+0]]))
        mtpart_splits_test[[2*i+0]]$Pnode   <- paste(nrow(split_df[[2*i+0]])/nrow(split_df[[1]]))
        mtpart_splits_test[[2*i+0]]$Targets <- splitL_eval
        mtpart_splits_test[[2*i+0]]$relerr  <- L_relerr
        # Record right-child node
        mtpart_splits_test[[2*i+1]]$N       <- paste(nrow(split_df[[2*i+1]]))
        mtpart_splits_test[[2*i+1]]$Pnode   <- paste(nrow(split_df[[2*i+1]])/nrow(split_df[[1]]))
        mtpart_splits_test[[2*i+1]]$Targets <- splitR_eval
        mtpart_splits_test[[2*i+1]]$relerr  <- R_relerr
      }
      else {
        # Record child dataframes
        split_df[[2*i+0]] <- splitL
        split_df[[2*i+1]] <- splitR
        splitZ[[2*i+0]] <- splitL_Z
        splitZ[[2*i+1]] <- splitR_Z
        splitX[[2*i+0]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitL))
        splitX[[2*i+1]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitR))
        misclass_targets_L <- misclass_targets_R <- as.list(1:length(splitZ[[i]]$Z))
        
      }
    }
    else if (nrow(df) == 1 & !is.null(mtpart_splits_test[[i]])) {
      root_eval <- MTSummary(targets=Z_test, data=data_test)
      mtpart_splits_test[[i]]$N       <- paste(nrow(data_test))
      mtpart_splits_test[[i]]$Pnode   <- paste(nrow(data_test)/nrow(data_test))
      mtpart_splits_test[[i]]$Targets <- root_eval
      temp   <- split_df[[i]]
    }
    else if (2*i>length(mtpart_splits_test) & !is.null(mtpart_splits_test[[i]])) {
      mtpart_splits_test[[i]]$Eval <- NA
    }
    else if (!is.null(mtpart_splits_test[[i]]) && !is.null(split_df[[i]]) && !is.null(mtpart_splits[[2*i]]) &&
             length(levels(droplevels(as.factor(split_df[[i]][,c(which(colnames(split_df[[i]])==(unlist(strsplit(mtpart_splits[[2*i]]$SplitVar, " ")))[1]))] ))))>2 &&
             2*i<=length(mtpart_splits_test)) {
      temp      <- split_df[[i]]
      splitvar  <- mtpart_splits[[2*i]]$SplitVar
      var       <- (unlist(strsplit(splitvar, " ")))[1]
      varnum    <- which(colnames(temp)==var)
      notation  <- (unlist(strsplit(splitvar, " ")))[2]
      thresh    <- (unlist(strsplit(splitvar, " ")))[3]
      ifelse(notation == "in", threshold <- str_remove(thresh, " in "),
             ifelse(notation == "<", threshold <- str_remove(thresh, " < "), NA))
      # Subset data based on selected split
      splitL_Z <- splitR_Z <- splitZ[[i]]
      ifelse(notation == "in", splitL <- (temp[which(temp[,c(varnum)] == threshold), c(1:ncol(temp))]),
             ifelse(notation == "<", splitL  <- (temp[which(temp[,c(varnum)] < as.numeric(threshold)), c(1:ncol(temp))]), NA))
      splitL_Z$Z <- subset(splitL_Z$Z, row.names(splitL_Z$Z) %in% row.names(splitL))
      ifelse(notation == "in", splitR <- (temp[which(temp[,c(varnum)] != threshold), c(1:ncol(temp))]),
             ifelse(notation == "<", splitR <- (temp[which(temp[,c(varnum)] >= as.numeric(threshold)), c(1:ncol(temp))]), NA))
      splitR_Z$Z <- subset(splitR_Z$Z, row.names(splitR_Z$Z) %in% row.names(splitR))
      ifelse(notation == "in", splitvarR <- paste(var, threshold, sep = " not in "),
             ifelse(notation == "<", splitvarR <- paste(var, threshold, sep = " >= "), NA))
      if (nrow(splitL_Z$Z)==0 | nrow(splitR_Z$Z)==0 | length(levels(temp[,c(varnum)]))==0) {mtpart_splits_test[[i]]$Eval <- mtpart_splits_test[[i-1]]$Eval}
      else {
        # Evaluate child nodes across targets using MTSummary
        splitL_eval <- try(suppressWarnings(MTSummary(splitL_Z, data=splitL)))
        splitR_eval <- try(suppressWarnings(MTSummary(splitR_Z, data=splitR)))
        # Evaluate split using CV error & sd (caret) --> Record for parent node
        misclass_targets_L <- misclass_targets_R <- as.list(1:length(splitZ[[i]]$Z))
        for (j in 1:length(splitL_eval)) {
          if(splitZ[[i]]$Definitions[j]=="Cat") {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$expectedloss/mtpart_splits_test[[1]]$Targets[[j]]$expectedloss
          }
          else if(splitZ[[i]]$Definitions[j] == "Surv") {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else if(splitZ[[i]]$Definitions[j] == "Count") {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else {
            splitL_eval[[j]]$relerr <- splitL_eval[[j]]$MSE/mtpart_splits_test[[1]]$Targets[[j]]$MSE
          }
          misclass_targets_L[[j]] <- splitL_eval[[j]]$relerr
        }
        ifelse(!is.null(wt), (L_relerr <- weighted.mean(as.numeric(misclass_targets_L), w=(wt), na.rm=TRUE)),
               (L_relerr <- mean(as.numeric(misclass_targets_L), na.rm = TRUE)))
        for (j in 1:length(splitR_eval)) {
          if(splitZ[[i]]$Definitions[j]=="Cat") {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$expectedloss/mtpart_splits_test[[1]]$Targets[[j]]$expectedloss
          }
          else if(splitZ[[i]]$Definitions[j] == "Surv") {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else if(splitZ[[i]]$Definitions[j] == "Count") {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$deviance/mtpart_splits_test[[1]]$Targets[[j]]$deviance
          }
          else {
            splitR_eval[[j]]$relerr <- splitR_eval[[j]]$MSE/mtpart_splits_test[[1]]$Targets[[j]]$MSE
          }
          misclass_targets_R[[j]] <- splitR_eval[[j]]$relerr
        }
        ifelse(!is.null(wt), (R_relerr <- weighted.mean(as.numeric(misclass_targets_R), w=(wt), na.rm=TRUE)),
               (R_relerr <- mean(as.numeric(misclass_targets_R), na.rm = TRUE)))
        mtpart_splits_test[[i]]$CP      <- mtpart_splits_test[[i]]$relerr - ((L_relerr + R_relerr)/2)
        splitCVeval <- CVsplitEval(splitvar, splitX[[i]], splitZ[[i]], split_df[[i]])
        mtpart_splits_test[[i]]$CVeval <- splitCVeval
        CVeval_Xerr_targets <- CVeval_Xstd_targets <- as.list(1:length(splitZ[[i]]$Z))
        for (j in 1:length(splitZ[[i]]$Z)) {
          if(splitZ[[i]]$Definitions[j]=="Cat") {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Accuracy)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$AccuracySD
          }
          else if(splitZ[[i]]$Definitions[j] == "Surv") {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Rsquared)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$RsquaredSD
          }
          else if(splitZ[[i]]$Definitions[j] == "Count") {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Rsquared)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$RsquaredSD
          }
          else {
            mtpart_splits_test[[i]]$CVeval[[j]]$Xerror <- (1 - mtpart_splits_test[[i]]$CVeval[[j]]$Rsquared)
            mtpart_splits_test[[i]]$CVeval[[j]]$Xstd   <- mtpart_splits_test[[i]]$CVeval[[j]]$RsquaredSD
          }
          CVeval_Xerr_targets[[j]] <- mtpart_splits_test[[i]]$CVeval[[j]]$Xerror
          CVeval_Xstd_targets[[j]] <- mtpart_splits_test[[i]]$CVeval[[j]]$Xstd
        }
        ifelse(!is.null(wt), (mtpart_splits_test[[i]]$SXerror <- (weighted.mean(as.numeric(CVeval_Xerr_targets), w=(wt), na.rm=TRUE))),
               (mtpart_splits_test[[i]]$SXerror <- (mean(as.numeric(CVeval_Xerr_targets)))))
        ifelse(!is.null(wt), (mtpart_splits_test[[i]]$SXstd <- ( weighted.mean(as.numeric(CVeval_Xstd_targets), w=(wt), na.rm=TRUE))),
               (mtpart_splits_test[[i]]$SXstd <- ( mean(as.numeric(CVeval_Xstd_targets)))))
        mtpart_splits_test[[i]]$Eval <- NA
        # Record child dataframes
        split_df[[2*i+0]] <- splitL
        split_df[[2*i+1]] <- splitR
        splitZ[[2*i+0]] <- splitL_Z
        splitZ[[2*i+1]] <- splitR_Z
        splitX[[2*i+0]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitL))
        splitX[[2*i+1]] <- subset(splitX[[i]], row.names(splitX[[i]]) %in% row.names(splitR))
        # Record left-child node
        mtpart_splits_test[[2*i+0]]$N       <- paste(nrow(split_df[[2*i+0]]))
        mtpart_splits_test[[2*i+0]]$Pnode   <- paste(nrow(split_df[[2*i+0]])/nrow(split_df[[1]]))
        mtpart_splits_test[[2*i+0]]$Targets <- splitL_eval
        mtpart_splits_test[[2*i+0]]$relerr  <- L_relerr
        # Record right-child node
        mtpart_splits_test[[2*i+1]]$N       <- paste(nrow(split_df[[2*i+1]]))
        mtpart_splits_test[[2*i+1]]$Pnode   <- paste(nrow(split_df[[2*i+1]])/nrow(split_df[[1]]))
        mtpart_splits_test[[2*i+1]]$Targets <- splitR_eval
        mtpart_splits_test[[2*i+1]]$relerr  <- R_relerr
      }
    }
    else if (!is.null(mtpart_splits_test[[i]]) & !is.null(split_df[[i]]) & 2*i<=length(mtpart_splits_test) & 2*i<length(mtpart_splits_test) &&
             is.null(mtpart_splits[[2*i]])) {
      mtpart_splits_test[[i]]$Eval <- NA
    }
    else { i <- i + 1 }
  }
  # Return test tree
  return(list(df, mtpart_splits_test))
}

# Function to prune the decision tree

MTPrune <- function(tree, targets, cp = 0.02, wt=NULL){
  # Extract parent-child relationships & assign tree level
  df <- tree[[1]]
  df[1,]$parent <- 0
  #df[which((df$child==1)), c(1:2)]$parent <- 0
  df <- df[which(!is.na(df$parent)), c(1:2)]
  mtpart_splits <- tree[[2]]
  df$level <- NA
  if (nrow(df)>1) {
    for (i in 2:nrow(df)) {
      n <- as.numeric((df[i,]$parent))
      df[i,]$level <- floor(log2(n)+1)
    }
  }
  df[1,]$level <- 0
  # Split error & complexity table
  summarytable <- matrix(ncol = (8), nrow = length(unique(df[c(1:nrow(df)),]$parent)))
  colnames(summarytable) <- c("CP", "nsplit", "RelError", "Xerror", "Xstd", "leaves", "eval", "error")
  parents <- unique(df[c(1:nrow(df)),]$parent)
  for (i in 1:length(parents)) {
    if (i == 1) {
      if (nrow(df) > 1) {n <- as.numeric(unique(df[c(2:nrow(df)),]$parent))[i]}
      else {n <- 1}
      summarytable[i,1] <- mtpart_splits[[n]]$CP
      summarytable[i,2] <- (i-1)
      summarytable[i,3] <- mtpart_splits[[n]]$relerr
      summarytable[i,4] <- mtpart_splits[[n]]$SXerror
      summarytable[i,5] <- mtpart_splits[[n]]$SXstd
      summarytable[i,6] <- i
      summarytable[i,7] <- (mtpart_splits[[n]]$SXerror + !is.na(mtpart_splits[[n]]$SXstd))
      relerrs  <- matrix(ncol = (length(mtpart_splits[[1]]$Targets)+1), nrow = (2^(i-1)) )
      colnames(relerrs) <- c(names(mtpart_splits[[1]]$Targets), "MultiTarget")
      for (z in 1:length(mtpart_splits[[1]]$Targets)) {
        if (targets$Definitions[z]=="Cont") {
          relerrs[1,z] <- as.numeric(as.character(mtpart_splits[[1]]$Targets[[z]]$MSE))
          #relerrs[l,z] <- as.numeric(as.character(trees[[r]][[l]]$Targets[[z]]$relerr))
        }
        else if (targets$Definitions[z]=="Cat") {
          relerrs[1,z] <- as.numeric(as.character(mtpart_splits[[1]]$Targets[[z]]$expectedloss))
          #relerrs[l,z] <- as.numeric(as.character(trees[[r]][[l]]$Targets[[z]]$relerr))
        }
        else {
          relerrs[1,z] <- as.numeric(as.character(mtpart_splits[[1]]$Targets[[z]]$deviance))
          #relerrs[l,z] <- as.numeric(as.character(trees[[r]][[l]]$Targets[[z]]$relerr))
        }
        #relerrs[[l]][[as.character(colnames(Ztype$Z)[z])]] <- trees[[r]][[l]]$Targets[[z]]$relerr
      }
      if (!is.null(wt)) {
        relerrs[1,(length(mtpart_splits[[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs[1,]), w=(wt), na.rm=TRUE)
      }
      else {
        #relerrs[l,(length(trees[[r]][[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs[l,]), w=(as.numeric(trees[[r]][[l]]$N)/as.numeric(trees[[r]][[1]]$N)), na.rm=TRUE)
        relerrs[1,(length(mtpart_splits[[1]]$Targets)+1)] <- mean(as.numeric(relerrs[1,]), na.rm=TRUE)
      }
      summarytable[i,8] <- mean(relerrs[, length(mtpart_splits[[1]]$Targets)+1], na.rm = TRUE)
    }
    else {
      df1 <- df[c(2:nrow(df)),]
      df1$rowid <- 1:nrow(df1)
      #Consider child & terminal nodes at or preceding parent i
      df_temp <- df1[which(as.numeric(df1$parent)<=(as.numeric(unique(df1[c(1:nrow(df1)),]$parent))[i-1])), c(1:ncol(df1))]
      df_temp$childleaf <- df_temp$childid <- NA
      for (x in 1:nrow(df_temp)) {
        df_temp[x,]$childid   <- unlist(strsplit(df_temp[x,]$child, " "))[[1]]
        df_temp[x,]$childleaf <- ifelse(length(unlist(strsplit(df_temp[x,]$child, " "))) >= 2, "1", "0")
        if (unlist(strsplit(df_temp[x,]$child, " "))[[1]] %in% df_temp$parent) {
          next
        }
        else if (length(unlist(strsplit(df_temp[x,]$child, " "))) < 2) {
          df_temp[x,]$child <- sub("^", df_temp[x,]$child, " *")
          df_temp[x,]$childleaf <- ifelse(length(unlist(strsplit(df_temp[x,]$child, " "))) >= 2, "1", "0")
        }
        else {
          next
        }
      }
      summarytable[i,2] <- (length(as.numeric(unique(df_temp$parent))))
      df_temp <- df_temp[which(as.numeric(df_temp$parent)==(as.numeric(unique(df1[c(1:nrow(df1)),]$parent))[i-1]) | df_temp$childleaf==1), c(1:ncol(df_temp))]
      relerr <- vector(mode = "list", length = length(as.numeric(unique(df_temp$childid)))) #CP <- nsplit <- SXerror <- SXstd <-
      Parent_split <- c(as.numeric(unique(df_temp[1:nrow(df_temp),]$parent)))
      Child_split <- c(as.numeric(unique(df_temp[1:nrow(df_temp),]$childid)))
      for (d in 1:length(Child_split)) {
        n <- as.numeric(Child_split[d])
        relerr[[d]]  <- mtpart_splits[[n]]$relerr
      }
      summarytable[i,1] <- mtpart_splits[[(as.numeric(unique(df1[c(1:nrow(df1)),]$parent))[i-1])]]$CP
      summarytable[i,3] <- mean(unlist(relerr), na.rm = TRUE)
      summarytable[i,4] <- mtpart_splits[[(as.numeric(unique(df1[c(1:nrow(df1)),]$parent))[i-1])]]$SXerror
      summarytable[i,5] <- mtpart_splits[[(as.numeric(unique(df1[c(1:nrow(df1)),]$parent))[i-1])]]$SXstd
      summarytable[i,6] <- summarytable[i,2] + 1
      summarytable[i,7] <- (summarytable[i,4] + !is.na(summarytable[i,5]))
      relerrs  <- matrix(ncol = (length(mtpart_splits[[1]]$Targets)+1), nrow =  length(mtpart_splits)) #(2^(i)-1)
      colnames(relerrs) <- c(names(mtpart_splits[[1]]$Targets), "MultiTarget")
      for (l in 1:length(mtpart_splits)) {
        nodeid    <- (unlist(strsplit(df_temp[which(df_temp$childid==l), c(1:ncol(df_temp))]$child, " ")))
        if (!is.null(mtpart_splits[[l]]) && (!is.na(mtpart_splits[[l]]$Targets))) {
          #nodeid    <- (unlist(strsplit(df_temp[which(df_temp$childid==l), c(1:ncol(df_temp))]$child, " ")))
          #nodeid    <- (unlist(strsplit(mtpart_splits[[l]]$NodeID, " ")))
          if (length(nodeid)>=2 ) {
            #if (length(nodeid)>=2 | ((2*l+1) > as.numeric((unlist(strsplit(tail(df_temp$child,n=1), " "))[[1]]))) ) {
            #if (length(nodeid)>=2 | ((2*l+1) > 2^(i)) ) {
            nodeprop <- as.numeric(mtpart_splits[[l]]$N)/as.numeric(mtpart_splits[[1]]$N)
            for (z in 1:length(mtpart_splits[[1]]$Targets)) {
              if (targets$Definitions[z]=="Cont") {
                relerrs[l,z] <- as.numeric(as.character(mtpart_splits[[l]]$Targets[[z]]$MSE))*nodeprop
                #relerrs[l,z] <- as.numeric(as.character(trees[[r]][[l]]$Targets[[z]]$relerr))
              }
              else if (targets$Definitions[z]=="Cat") {
                relerrs[l,z] <- as.numeric(as.character(mtpart_splits[[l]]$Targets[[z]]$expectedloss))*nodeprop
                #relerrs[l,z] <- as.numeric(as.character(trees[[r]][[l]]$Targets[[z]]$relerr))
              }
              else {
                relerrs[l,z] <- as.numeric(as.character(mtpart_splits[[l]]$Targets[[z]]$deviance))*nodeprop
                #relerrs[l,z] <- as.numeric(as.character(trees[[r]][[l]]$Targets[[z]]$relerr))
              }
              #relerrs[[l]][[as.character(colnames(Ztype$Z)[z])]] <- trees[[r]][[l]]$Targets[[z]]$relerr
            }
            if (!is.null(wt)) {
              relerrs[l,(length(mtpart_splits[[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs[l,]), w=(wt * (as.numeric(mtpart_splits[[l]]$N)/as.numeric(mtpart_splits[[1]]$N))), na.rm=TRUE)
            }
            else {
              #relerrs[l,(length(trees[[r]][[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs[l,]), w=(as.numeric(trees[[r]][[l]]$N)/as.numeric(trees[[r]][[1]]$N)), na.rm=TRUE)
              relerrs[l,(length(mtpart_splits[[1]]$Targets)+1)] <- mean(as.numeric(relerrs[l,]), na.rm=TRUE)
            }
          }
          else {
            #relerrs[c(l),] <- NA
            next
          }
        }
        else {
          #relerrs[c(l),] <- NA
          next
        }
      }
      if (!is.null(wt)) {
        relerrs[1,(length(mtpart_splits[[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs[1,]), w=(wt), na.rm=TRUE)
      }
      else {
        relerrs[1,(length(mtpart_splits[[1]]$Targets)+1)] <- mean(as.numeric(relerrs[1,]), na.rm=TRUE)
      }
      summarytable[i,8] <- mean(relerrs[, length(mtpart_splits[[1]]$Targets)+1], na.rm = TRUE)
    }
  }
  # Prune nodes if: CP < cp, then take min(xerror + xstd)
  cptable   <- data.frame(summarytable)
  cptable$parent <- (as.numeric(as.character(unique(df$parent))))
  cptable$keep <- NA
  for (i in 1:nrow(cptable)) {
    if(!is.na(cptable[i,]$CP) & cptable[i,]$CP >= cp){
      cptable[i,]$keep <- 1
      children <- as.numeric(as.character(gsub( " .*$", "", df$child )))
      #children <- (as.numeric(as.character(df$child)))
      if (cptable[i,]$parent %in% children) {
        getpar <- (as.numeric(as.character(df[which(as.numeric(as.character(gsub( " .*$", "", df$child )))==cptable[i,]$parent), c(1:ncol(df))]$parent)))
        cptable[which(cptable$parent==getpar),]$keep <- 1
      }
      #else {next}
    }
    else {
      if (cptable[i,]$parent==0) {
        cptable[i,]$keep <- 1
        cptable[i,]$eval <- 0
      }
      else {
        cptable[i,]$keep <- 0
      }
    }
  }
  #ifelse((cptable$CP) >= cp, cptable$keep <- 1, cptable$keep <- 0)
  cptable <- cptable[which(!is.na(cptable$eval)), c(1:ncol(cptable))]
  maxparent <- cptable[which(cptable$eval==min(cptable$eval)), c(1:ncol(cptable))]$parent
  keep      <- (cptable[which(cptable$keep==1 & cptable$parent <= maxparent), c(1:ncol(cptable))]$parent)#+1
  df$parent <- as.numeric(as.character(df$parent))
  # Update parent-child table ###### NOTE: update keep indexing for trees with multiple splits per level
  keepdf    <- df[which(df$parent %in% keep), c(1:2)]
  keepdf$childid <- NA
  for (c in 1:nrow(keepdf)) {
    keepdf[c,]$childid <- unlist(strsplit(keepdf[c,]$child, " "))[[1]]
    if (unlist(strsplit(keepdf[c,]$child, " "))[1] %in% keepdf$parent) {
      keepdf[c,]$child <- keepdf[c,]$child
    }
    else if (length(unlist(strsplit(keepdf[c,]$child, " "))) < 2) {
      keepdf[c,]$child <- sub("^", keepdf[c,]$child, " *")
    }
    else {
      keepdf[c,]$child <- keepdf[c,]$child
    }
  }
  # Update decision tree
  keepnodes <- as.list(1:length(mtpart_splits))
  for (n in 1:length(mtpart_splits)) {
    if (n %in% c(unique(keepdf$parent))) {
      keepnodes[[n]] <- mtpart_splits[[n]]
    }
    else if (n %in% c(as.numeric(keepdf$childid))) {
      keepnodes[[n]] <- mtpart_splits[[n]]
      if (length(unlist(strsplit(mtpart_splits[[n]]$NodeID, " "))) < 2) {
        keepnodes[[n]]$NodeID <- sub("^", mtpart_splits[[n]]$NodeID, " *")
      }
      else {
        keepnodes[[n]]$NodeID <- keepnodes[[n]]$NodeID
        next
      }
    }
    else {
      keepnodes[n] <- list(NULL)
      next
    }
  }
  return(list(keepdf[,c(1:2)], keepnodes, summarytable)) #consider outputting eval directly instead of raw datasets
}


# CART multi-target evaluation of unpruned & pruned model on training & testing data

CART_MTEval <- function(depth, data, testdata=NULL, targets, outcome, Equation, method, cp=0.001, wt=NULL, minsplit=20){
  cartnames <- matrix(ncol = (3), nrow=0)
  colnames(cartnames) <- c("target","eval","depth")
  #Extract Leaf Nodes for Multi-Target Summaries
  tree <- cols           <- vector(mode = "list", length = depth+1)
  tree[[1]][[1]]$N       <- (nrow(data))
  tree[[1]][[1]]$Targets <- MTSummary(targets, data)
  tree_prune                   <- vector(mode = "list", length = depth+1)
  tree_prune[[1]][[1]]$N       <- (nrow(data))
  tree_prune[[1]][[1]]$Targets <- MTSummary(targets, data)
  if (!is.null(testdata)) {
    treetest                   <- vector(mode = "list", length = depth+1)
    treetest[[1]][[1]]$N       <- (nrow(testdata))
    treetest[[1]][[1]]$Targets <- MTSummary(targets, testdata)
    treetest_prune                   <- vector(mode = "list", length = depth+1)
    treetest_prune[[1]][[1]]$N       <- (nrow(testdata))
    treetest_prune[[1]][[1]]$Targets <- MTSummary(targets, testdata)
  }
  #else {next}
  cartnames            <- rbind(cartnames, c(outcome,"CART",1) )
  for (r in 1:depth) {
    cartnames <- rbind(cartnames, c(outcome,"CART",(r+1)))
    #Run model in cart for all desired depths (maxdepth = MTPart depth-1)
    fit <- rpart(Equation, data = data, method=method, cp=0.0, control = rpart.control(maxdepth = r, minsplit = minsplit))
    #Extract tree rules and subset data for unpruned training MTSummary leaf node evalutation (comparable with MTPart)
    fitrules <- rpart.rules(fit, style = "tall")
    if (!any(fitrules=="null model")) {
      nodelist <- vector(mode = "list", length = nrow(fitrules))
      for (i in 1:nrow(fitrules)) {
        #fitrules_i <- fitrules[i,]#[!sapply(fitrules[i,], function(x) all(x == ""))]
        fitrules_i <- fitrules[i,][!sapply((rpart.rules(fit, style="tall"))[i,], function(x) all(x == ""))]
        #fitrules_i
        colnum <- varval <- vector(mode = "list", length = (r))
        for (d in 1:r) {
          if ((3+(4*(d-1))) <= ncol(fitrules_i) && fitrules_i[,c(3+(4*(d-1)))] !="" || (3+(2*(d-1))) <= ncol(fitrules_i) && fitrules_i[,c(3+(2*(d-1)))] !="") {
            if (any(fitrules_i[,c(1:ncol(fitrules_i))]=="to")) {
              if ((6+(4*(d-1)) <= ncol(fitrules_i))) {
                if (fitrules_i[,(6+(4*(d-1)))]=="to") {
                  colnum[[d]]      <- which(colnames(data)==fitrules_i[,(3+(4*(d-1)))])
                  varclass         <- class(data[,colnum[[d]]])
                  varval[[d]]      <- paste(fitrules_i[,(5+(4*(d-1)))], fitrules_i[,(6+(4*(d-1)))], fitrules_i[,(7+(4*(d-1)))])
                }
                else if (any((fitrules_i[,(1:ncol(fitrules_i))]=="to")[1:(3+(4*(d-1)))])) {
                  colnum[[d]]      <- which(colnames(data)==fitrules_i[,(5+(4*(d-1)))])
                  varclass         <- class(data[,colnum[[d]]])
                  ifelse(varclass=="integer" | varclass=="numeric",
                         (varval[[d]] <- as.numeric(as.character(fitrules_i[,(7+(4*(d-1)))]))),
                         (varval[[d]] <- fitrules_i[,(7+(4*(d-1)))]))
                }
                else {
                  colnum[[d]]      <- which(colnames(data)==fitrules_i[,(3+(4*(d-1)))])
                  varclass         <- class(data[,colnum[[d]]])
                  ifelse(varclass=="integer" | varclass=="numeric",
                         (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                         (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
                }
              }
              else {
                next
              }
            }
            else {
              if ((3+(4*(d-1))) <= ncol(fitrules_i) && (fitrules_i[,(3+(4*(d-1)))]) %in% colnames(data)) {
                colnum[[d]]      <- (which(colnames(data)==fitrules_i[,(3+(4*(d-1)))]))
                varclass         <- class(data[,colnum[[d]]])
                ifelse(varclass=="integer" | varclass=="numeric",
                       (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                       (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
              }
              else if ((3+(2*(d-1))) <= ncol(fitrules_i) && (fitrules_i[,(3+(2*(d-1)))]) %in% colnames(data)) {
                colnum[[d]]      <- (which(colnames(data)==fitrules_i[,(3+(2*(d-1)))]))
                varclass         <- class(data[,colnum[[d]]])
                ifelse(varclass=="integer" | varclass=="numeric",
                       (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(2*(d-1)))]))),
                       (varval[[d]] <- fitrules_i[,(5+(2*(d-1)))]))
              }
              else {
                if ((4+(4*(d-1))) <= ncol(fitrules_i) && fitrules_i[,(4+(4*(d-1)))] %in% colnames(data)) {
                  colnum[[d]]      <- (which(colnames(data)==fitrules_i[,(4+(4*(d-1)))]))
                  varclass         <- class(data[,colnum[[d]]])
                  ifelse(varclass=="integer" | varclass=="numeric",
                         (varval[[d]] <- as.numeric(as.character(fitrules_i[,(6+(4*(d-1)))]))),
                         (varval[[d]] <- fitrules_i[,(6+(4*(d-1)))]))
                }
                else if ((3+(3*(d-1))) <= ncol(fitrules_i) && fitrules_i[,(3+(3*(d-1)))] %in% colnames(data)) {
                  colnum[[d]]      <- (which(colnames(data)==fitrules_i[,(3+(3*(d-1)))]))
                  varclass         <- class(data[,colnum[[d]]])
                  ifelse(varclass=="integer" | varclass=="numeric",
                         (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(3*(d-1)))]))),
                         (varval[[d]] <- fitrules_i[,(6+(4*(d-1)))]))
                }
                else if ((3+(3*(d-3))) <= ncol(fitrules_i) && (3+(3*(d-3))) > 0 && fitrules_i[,(3+(3*(d-3)))] %in% colnames(data)) {
                  colnum[[d]]      <- (which(colnames(data)==fitrules_i[,(3+(3*(d-3)))]))
                  varclass         <- class(data[,colnum[[d]]])
                  varval[[d]] <- as.numeric(as.character(unlist(fitrules_i[,(3+(3*(d-3))+2):ncol(fitrules_i)])))[which(!is.na(as.numeric(as.character(unlist(fitrules_i[,(3+(3*(d-3))+2):ncol(fitrules_i)])))))]
                }
                else {
                  colnum[[d]]      <- (which(colnames(data)==fitrules_i[,(3+(3*(d-2)))]))
                  varclass         <- class(data[,colnum[[d]]])
                  ifelse(varclass=="integer" | varclass=="numeric",
                         (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(3*(d-2)))]))),
                         (varval[[d]] <- fitrules_i[,(5+(3*(d-2)))]))
                }
              }
            }
          }
          else {
            next
          }
        }
        cols[[r+1]]  <- Filter(Negate(is.null), colnum)
        defs         <- vector(mode = "list", length = length(varval))
        for (d in 1:r) {
          if (d <= length(varval) & !is.null(varval[[d]])) {
            if (grepl("or", as.character(varval[[d]]), fixed = TRUE)) {
              opt1 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][1]
              opt2 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][2]
              defs[[d]] <- data[which(data[,colnum[[d]]]== opt1 | data[,colnum[[d]]]== opt2), c(1:ncol(data))]
            }
            else if (grepl(" to ", as.character(varval[[d]]), fixed = TRUE)) {
              opt1 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][1]
              opt2 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][2]
              defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(opt1)) & data[,colnum[[d]]] <= as.numeric(as.character(opt2))),
                                c(1:ncol(data))]
            }
            else {
              if (class(data[,colnum[[d]]])=="integer" | class(data[,colnum[[d]]])=="numeric") {
                #If numeric variable
                if (4+(4*(d-1)) <= ncol(fitrules_i)) {
                  (ifelse(fitrules_i[,(4+(4*(d-1)))]=="< ",
                          #Designate rules for < vs. >=
                          (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                          (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                }
                else {
                  if (4+(4*(d-2)) <= ncol(fitrules_i)) {
                    (ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                            #Designate rules for < vs. >=
                            (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                            (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                  }
                  else {
                    if (4+(4*(d-3)) <= ncol(fitrules_i)) {
                      (ifelse(fitrules_i[,(4+(4*(d-3)))]=="< ",
                              #Designate rules for < vs. >=
                              (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                              (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                    }
                    else {
                      if (4+(4*(d-4)) <= ncol(fitrules_i)) {
                        (ifelse(fitrules_i[,(4+(4*(d-4)))]=="< ",
                                #Designate rules for < vs. >=
                                (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                                (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                      }
                      else {
                        (ifelse(fitrules_i[,(4+(4*(d-5)))]=="< ",
                                #Designate rules for < vs. >=
                                (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                                (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                      }
                    }
                  }
                  #(ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                  #        #Designate rules for < vs. >=
                  #        (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                  #        (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                }
              }
              else {
                (defs[[d]] <- data[which(data[,colnum[[d]]]==varval[[d]]), c(1:ncol(data))] )
              }
            }
          }
          else {
            next
          }
        }
        defs <- Filter(Negate(is.null), defs)
        nodedata    <- Reduce(function(dtf1, dtf2) merge(dtf1, dtf2, all=TRUE), defs)
        nodeoutputs <- targets
        #nodeoutputs[[2]] <- nodedata[,c(40,44,53,127,134:136)] #update to relevant target cols
        nodeoutputs[[2]] <- nodedata[,c(which(colnames(data) %in% colnames(targets[[2]])))] #update to relevant target cols
        #prep <- suppressWarnings(SplitPrep(Xdf=splitX[[i]], df=split_df[[i]], data_splt=split_df[[1]], parentsplit))
        #eval_temp <- NA
        #eval_temp <- suppressWarnings(MultiEval(X=data.frame(prep[[1]]), splitZ[[i]], data=prep[[2]], continuous = continuous, quantseq = quantseq, wt = wt, evalmethod = evalmethod, alpha = alpha, IGcutoff = IGcutoff))
        nodelist[[i]]$N       <- (nrow(nodedata))
        if (nrow(nodedata) >= 1) {
          nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata)
        }
        else {nodelist[[i]]$Targets <- NULL}
        rm(varval, colnum)
      }
      #tree[[r+1]]$N <- print(nrow(nodedata))
      tree[[r+1]] <- nodelist
    }
    else {tree[[r+1]] <- tree[[1]] }
    #Test unpruned tree on test dataset
    if (!is.null(testdata)) {
      fitrules <- rpart.rules(fit,style = "tall")
      if (!any(fitrules=="null model")) {
        nodelist <- vector(mode = "list", length = nrow(fitrules))
        for (i in 1:nrow(fitrules)) {
          fitrules_i <- fitrules[i,][!sapply(fitrules[i,], function(x) all(x == ""))]
          colnum <- varval <- vector(mode = "list", length = (r))
          for (d in 1:r) {
            if ((3+(4*(d-1))) <= ncol(fitrules_i)) {
              if (any(fitrules_i[,c(1:ncol(fitrules_i))]=="to")) {
                if ((6+(4*(d-1)) <= ncol(fitrules_i))) {
                  if (fitrules_i[,(6+(4*(d-1)))]=="to") {
                    colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(3+(4*(d-1)))])
                    varclass         <- class(testdata[,colnum[[d]]])
                    varval[[d]]      <- paste(fitrules_i[,(5+(4*(d-1)))], fitrules_i[,(6+(4*(d-1)))], fitrules_i[,(7+(4*(d-1)))])
                  }
                  else if (any((fitrules_i[,(1:ncol(fitrules_i))]=="to")[1:(3+(4*(d-1)))])) {
                    colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(5+(4*(d-1)))])
                    varclass         <- class(testdata[,colnum[[d]]])
                    ifelse(varclass=="integer" | varclass=="numeric",
                           (varval[[d]] <- as.numeric(as.character(fitrules_i[,(7+(4*(d-1)))]))),
                           (varval[[d]] <- fitrules_i[,(7+(4*(d-1)))]))
                  }
                  else {
                    colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(3+(4*(d-1)))])
                    varclass         <- class(testdata[,colnum[[d]]])
                    ifelse(varclass=="integer" | varclass=="numeric",
                           (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                           (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
                  }
                }
                else {
                  next
                }
              }
              else {
                colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(3+(4*(d-1)))])
                varclass         <- class(testdata[,colnum[[d]]])
                ifelse(varclass=="integer" | varclass=="numeric",
                       (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                       (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
              }
            }
            else {
              next
            }
          }
          defs       <- vector(mode = "list", length = length(varval))
          for (d in 1:r) {
            if (d <= length(varval) & !is.null(varval[[d]])) {
              if (grepl("or", as.character(varval[[d]]), fixed = TRUE)) {
                opt1 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][1]
                opt2 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][2]
                defs[[d]] <- testdata[which(testdata[,colnum[[d]]]== opt1 | testdata[,colnum[[d]]]== opt2), c(1:ncol(testdata))]
              }
              else if (grepl(" to ", as.character(varval[[d]]), fixed = TRUE)) {
                opt1 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][1]
                opt2 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][2]
                defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(opt1)) & testdata[,colnum[[d]]] <= as.numeric(as.character(opt2))),
                                      c(1:ncol(testdata))]
              }
              else {
                if (class(testdata[,colnum[[d]]])=="integer" | class(testdata[,colnum[[d]]])=="numeric") {
                  #If numeric variable
                  if (4+(4*(d-1)) <= ncol(fitrules_i)) {
                    (ifelse(fitrules_i[,(4+(4*(d-1)))]=="< ",
                            #Designate rules for < vs. >=
                            (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                            (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                  }
                  else {
                    if (4+(4*(d-2)) <= ncol(fitrules_i)) {
                      (ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                              #Designate rules for < vs. >=
                              (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                              (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                    }
                    else {
                      if (4+(4*(d-3)) <= ncol(fitrules_i)) {
                        (ifelse(fitrules_i[,(4+(4*(d-3)))]=="< ",
                                #Designate rules for < vs. >=
                                (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                                (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                      }
                      else {
                        if (4+(4*(d-4)) <= ncol(fitrules_i)) {
                          (ifelse(fitrules_i[,(4+(4*(d-4)))]=="< ",
                                  #Designate rules for < vs. >=
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                        }
                        else {
                          (ifelse(fitrules_i[,(4+(4*(d-5)))]=="< ",
                                  #Designate rules for < vs. >=
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                        }
                      }
                    }
                    #(ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                    #        #Designate rules for < vs. >=
                    #        (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                    #        (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                  }
                }
                else {
                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]]==varval[[d]]), c(1:ncol(testdata))] )
                }
              }
            }
            else {
              next
            }
          }
          defs        <- Filter(Negate(is.null), defs)
          nodedata    <- Reduce(function(dtf1, dtf2) merge(dtf1, dtf2, all=TRUE), defs)
          nodeoutputs <- targets
          #nodeoutputs[[2]] <- nodedata[,c(40,44,53,127,134:136)]
          nodeoutputs[[2]] <- nodedata[,c(which(colnames(data) %in% colnames(targets[[2]])))] #update to relevant target cols
          #prep <- suppressWarnings(SplitPrep(Xdf=splitX[[i]], df=split_df[[i]], data_splt=split_df[[1]], parentsplit))
          #eval_temp <- NA
          #eval_temp <- suppressWarnings(MultiEval(X=data.frame(prep[[1]]), splitZ[[i]], data=prep[[2]], continuous = continuous, quantseq = quantseq, wt = wt, evalmethod = evalmethod, alpha = alpha, IGcutoff = IGcutoff))
          ifelse(nrow(nodedata) > 0, nodelist[[i]]$N <- (nrow(nodedata)), NA)
          #nodelist[[i]]$N       <- (nrow(nodedata))
          ifelse(nodelist[[i]]$N > 0, nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata), NA) #
          #nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata)
          rm(varval, colnum)
        }
        #tree[[r+1]]$N <- print(nrow(nodedata))
        #Remove terminal empty terminal nodes (test tree)
        nodelist <- Filter(Negate(is.null), nodelist)
        treetest[[r+1]] <- nodelist
      }
      else { treetest[[r+1]] <- treetest[[1]] }
    }
    #else {next}
    #Prune tree to desired cp
    fitprune <- prune(fit, cp)
    #Extract tree rules and subset data for pruned training MTSummary leaf node evalutation (comparable with MTPart)
    fitrules <- rpart.rules(fitprune,style = "tall")
    if (!any(fitrules=="null model")) {
      nodelist <- vector(mode = "list", length = nrow(fitrules))
      for (i in 1:nrow(fitrules)) {
        fitrules_i <- fitrules[i,][!sapply(fitrules[i,], function(x) all(x == ""))]
        colnum <- varval <- vector(mode = "list", length = (r))
        for (d in 1:r) {
          if ((3+(4*(d-1))) <= ncol(fitrules_i)) {
            if (any(fitrules_i[,c(1:ncol(fitrules_i))]=="to")) {
              if ((6+(4*(d-1)) <= ncol(fitrules_i))) {
                if (fitrules_i[,(6+(4*(d-1)))]=="to") {
                  colnum[[d]]      <- which(colnames(data)==fitrules_i[,(3+(4*(d-1)))])
                  varclass         <- class(data[,colnum[[d]]])
                  varval[[d]]      <- paste(fitrules_i[,(5+(4*(d-1)))], fitrules_i[,(6+(4*(d-1)))], fitrules_i[,(7+(4*(d-1)))])
                }
                else if (any((fitrules_i[,(1:ncol(fitrules_i))]=="to")[1:(3+(4*(d-1)))])) {
                  colnum[[d]]      <- which(colnames(data)==fitrules_i[,(5+(4*(d-1)))])
                  varclass         <- class(data[,colnum[[d]]])
                  ifelse(varclass=="integer" | varclass=="numeric",
                         (varval[[d]] <- as.numeric(as.character(fitrules_i[,(7+(4*(d-1)))]))),
                         (varval[[d]] <- fitrules_i[,(7+(4*(d-1)))]))
                }
                else {
                  colnum[[d]]      <- which(colnames(data)==fitrules_i[,(3+(4*(d-1)))])
                  varclass         <- class(data[,colnum[[d]]])
                  ifelse(varclass=="integer" | varclass=="numeric",
                         (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                         (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
                }
              }
              else {
                next
              }
            }
            else {
              colnum[[d]]      <- which(colnames(data)==fitrules_i[,(3+(4*(d-1)))])
              varclass         <- class(data[,colnum[[d]]])
              ifelse(varclass=="integer" | varclass=="numeric",
                     (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                     (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
            }
          }
          else {
            next
          }
        }
        defs       <- vector(mode = "list", length = length(varval))
        for (d in 1:r) {
          if (d <= length(varval) & !is.null(varval[[d]])) {
            if (grepl("or", as.character(varval[[d]]), fixed = TRUE)) {
              opt1 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][1]
              opt2 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][2]
              defs[[d]] <- data[which(data[,colnum[[d]]]== opt1 | data[,colnum[[d]]]== opt2), c(1:ncol(data))]
            }
            else if (grepl(" to ", as.character(varval[[d]]), fixed = TRUE)) {
              opt1 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][1]
              opt2 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][2]
              defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(opt1)) & data[,colnum[[d]]] <= as.numeric(as.character(opt2))),
                                c(1:ncol(data))]
            }
            else {
              if (class(data[,colnum[[d]]])=="integer" | class(data[,colnum[[d]]])=="numeric") {
                #If numeric variable
                if (4+(4*(d-1)) <= ncol(fitrules_i)) {
                  (ifelse(fitrules_i[,(4+(4*(d-1)))]=="< ",
                          #Designate rules for < vs. >=
                          (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                          (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                }
                else {
                  if (4+(4*(d-2)) <= ncol(fitrules_i)) {
                    (ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                            #Designate rules for < vs. >=
                            (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                            (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                  }
                  else {
                    if (4+(4*(d-3)) <= ncol(fitrules_i)) {
                      (ifelse(fitrules_i[,(4+(4*(d-3)))]=="< ",
                              #Designate rules for < vs. >=
                              (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                              (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                    }
                    else {
                      if (4+(4*(d-4)) <= ncol(fitrules_i)) {
                        (ifelse(fitrules_i[,(4+(4*(d-4)))]=="< ",
                                #Designate rules for < vs. >=
                                (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                                (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                      }
                      else {
                        (ifelse(fitrules_i[,(4+(4*(d-5)))]=="< ",
                                #Designate rules for < vs. >=
                                (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                                (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                      }
                    }
                  }
                  #(ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                  #        #Designate rules for < vs. >=
                  #        (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                  #        (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                }
              }
              else {
                (defs[[d]] <- data[which(data[,colnum[[d]]]==varval[[d]]), c(1:ncol(data))] )
              }
            }
          }
          else {
            next
          }
        }
        defs <- Filter(Negate(is.null), defs)
        nodedata    <- Reduce(function(dtf1, dtf2) merge(dtf1, dtf2, all=TRUE), defs)
        nodeoutputs <- targets
        #nodeoutputs[[2]] <- nodedata[,c(40,44,53,127,134:136)]
        nodeoutputs[[2]] <- nodedata[,c(which(colnames(data) %in% colnames(targets[[2]])))] #update to relevant target cols
        #prep <- suppressWarnings(SplitPrep(Xdf=splitX[[i]], df=split_df[[i]], data_splt=split_df[[1]], parentsplit))
        #eval_temp <- NA
        #eval_temp <- suppressWarnings(MultiEval(X=data.frame(prep[[1]]), splitZ[[i]], data=prep[[2]], continuous = continuous, quantseq = quantseq, wt = wt, evalmethod = evalmethod, alpha = alpha, IGcutoff = IGcutoff))
        nodelist[[i]]$N       <- (nrow(nodedata))
        ifelse(nodelist[[i]]$N > 0, nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata), nodelist[[i]]$Targets <- NA)
        #nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata)
        rm(varval, colnum)
      }
      #tree[[r+1]]$N <- print(nrow(nodedata))
      tree_prune[[r+1]] <- nodelist
    }
    else { tree_prune[[r+1]] <- tree_prune[[1]] }
    #Test pruned tree on test dataset
    if (!is.null(testdata)) {
      fitrules <- rpart.rules(fit,style = "tall")
      if (!any(fitrules=="null model")) {
        nodelist <- vector(mode = "list", length = nrow(fitrules))
        for (i in 1:nrow(fitrules)) {
          fitrules_i <- fitrules[i,][!sapply(fitrules[i,], function(x) all(x == ""))]
          colnum <- varval <- vector(mode = "list", length = (r))
          for (d in 1:r) {
            if ((3+(4*(d-1))) <= ncol(fitrules_i)) {
              if (any(fitrules_i[,c(1:ncol(fitrules_i))]=="to")) {
                if ((6+(4*(d-1)) <= ncol(fitrules_i))) {
                  if (fitrules_i[,(6+(4*(d-1)))]=="to") {
                    colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(3+(4*(d-1)))])
                    varclass         <- class(testdata[,colnum[[d]]])
                    varval[[d]]      <- paste(fitrules_i[,(5+(4*(d-1)))], fitrules_i[,(6+(4*(d-1)))], fitrules_i[,(7+(4*(d-1)))])
                  }
                  else if (any((fitrules_i[,(1:ncol(fitrules_i))]=="to")[1:(3+(4*(d-1)))])) {
                    colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(5+(4*(d-1)))])
                    varclass         <- class(testdata[,colnum[[d]]])
                    ifelse(varclass=="integer" | varclass=="numeric",
                           (varval[[d]] <- as.numeric(as.character(fitrules_i[,(7+(4*(d-1)))]))),
                           (varval[[d]] <- fitrules_i[,(7+(4*(d-1)))]))
                  }
                  else {
                    colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(3+(4*(d-1)))])
                    varclass         <- class(testdata[,colnum[[d]]])
                    ifelse(varclass=="integer" | varclass=="numeric",
                           (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                           (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
                  }
                }
                else {
                  next
                }
              }
              else {
                colnum[[d]]      <- which(colnames(testdata)==fitrules_i[,(3+(4*(d-1)))])
                varclass         <- class(testdata[,colnum[[d]]])
                ifelse(varclass=="integer" | varclass=="numeric",
                       (varval[[d]] <- as.numeric(as.character(fitrules_i[,(5+(4*(d-1)))]))),
                       (varval[[d]] <- fitrules_i[,(5+(4*(d-1)))]))
              }
            }
            else {
              next
            }
          }
          defs       <- vector(mode = "list", length = length(varval))
          for (d in 1:r) {
            if (d <= length(varval) & !is.null(varval[[d]])) {
              if (grepl("or", as.character(varval[[d]]), fixed = TRUE)) {
                opt1 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][1]
                opt2 <- strsplit(as.character(varval[[d]]), split=" or ")[[1]][2]
                defs[[d]] <- testdata[which(testdata[,colnum[[d]]]== opt1 | testdata[,colnum[[d]]]== opt2), c(1:ncol(testdata))]
              }
              else if (grepl(" to ", as.character(varval[[d]]), fixed = TRUE)) {
                opt1 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][1]
                opt2 <- strsplit(as.character(varval[[d]]), split=" to ")[[1]][2]
                defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(opt1)) & testdata[,colnum[[d]]] <= as.numeric(as.character(opt2))),
                                      c(1:ncol(testdata))]
              }
              else {
                if (class(testdata[,colnum[[d]]])=="integer" | class(testdata[,colnum[[d]]])=="numeric") {
                  #If numeric variable
                  if (4+(4*(d-1)) <= ncol(fitrules_i)) {
                    (ifelse(fitrules_i[,(4+(4*(d-1)))]=="< ",
                            #Designate rules for < vs. >=
                            (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                            (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                  }
                  else {
                    if (4+(4*(d-2)) <= ncol(fitrules_i)) {
                      (ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                              #Designate rules for < vs. >=
                              (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                              (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                    }
                    else {
                      if (4+(4*(d-3)) <= ncol(fitrules_i)) {
                        (ifelse(fitrules_i[,(4+(4*(d-3)))]=="< ",
                                #Designate rules for < vs. >=
                                (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                                (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                      }
                      else {
                        if (4+(4*(d-4)) <= ncol(fitrules_i)) {
                          (ifelse(fitrules_i[,(4+(4*(d-4)))]=="< ",
                                  #Designate rules for < vs. >=
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                        }
                        else {
                          (ifelse(fitrules_i[,(4+(4*(d-5)))]=="< ",
                                  #Designate rules for < vs. >=
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] ),
                                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(testdata))] )))
                        }
                      }
                    }
                    #(ifelse(fitrules_i[,(4+(4*(d-2)))]=="< ",
                    #        #Designate rules for < vs. >=
                    #        (defs[[d]] <- data[which(data[,colnum[[d]]] <  as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] ),
                    #        (defs[[d]] <- data[which(data[,colnum[[d]]] >= as.numeric(as.character(varval[[d]]))), c(1:ncol(data))] )))
                  }
                }
                else {
                  (defs[[d]] <- testdata[which(testdata[,colnum[[d]]]==varval[[d]]), c(1:ncol(testdata))] )
                }
              }
            }
            else {
              next
            }
          }
          defs <- Filter(Negate(is.null), defs)
          nodedata    <- Reduce(function(dtf1, dtf2) merge(dtf1, dtf2, all=TRUE), defs)
          nodeoutputs <- targets
          #nodeoutputs[[2]] <- nodedata[,c(40,44,53,127,134:136)]
          nodeoutputs[[2]] <- nodedata[,c(which(colnames(data) %in% colnames(targets[[2]])))] #update to relevant target cols
          #prep <- suppressWarnings(SplitPrep(Xdf=splitX[[i]], df=split_df[[i]], data_splt=split_df[[1]], parentsplit))
          #eval_temp <- NA
          #eval_temp <- suppressWarnings(MultiEval(X=data.frame(prep[[1]]), splitZ[[i]], data=prep[[2]], continuous = continuous, quantseq = quantseq, wt = wt, evalmethod = evalmethod, alpha = alpha, IGcutoff = IGcutoff))
          ifelse(nrow(nodedata) > 0, nodelist[[i]]$N <- (nrow(nodedata)), NA)
          #nodelist[[i]]$N       <- (nrow(nodedata))
          ifelse(nodelist[[i]]$N > 0, nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata), NA) #
          #nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata)
          #ifelse(nodelist[[i]]$N > 0, nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata), nodelist[[i]]$Targets <- NA)
          #nodelist[[i]]$Targets <- MTSummary(nodeoutputs, nodedata)
          rm(varval, colnum)
        }
        #tree[[r+1]]$N <- print(nrow(nodedata))
        nodelist <- Filter(Negate(is.null), nodelist)
        treetest_prune[[r+1]] <- nodelist
      }
      else { treetest_prune[[r+1]] <- treetest_prune[[1]] }
    }
    #else {next}
  }
  #Extract & Tabulate Training Error for Unpruned & Pruned Trees
  cart_evals           <- matrix(ncol = (length(tree[[1]][[1]]$Targets)+1), nrow = (depth+1))
  colnames(cart_evals) <- c(names(tree[[1]][[1]]$Targets), "MultiTarget")
  carterrslist         <- vector(mode = "list", length = length(depth+1))
  cart_evals_prune           <- matrix(ncol = (length(tree_prune[[1]][[1]]$Targets)+1), nrow = (depth+1))
  colnames(cart_evals_prune) <- c(names(tree_prune[[1]][[1]]$Targets), "MultiTarget")
  cartperrslist              <- vector(mode = "list", length = length(depth+1))
  for (r in 1:(depth+1)) {
    cartdepth <- length(tree[[r]])
    relerrs   <- matrix(ncol = (length(tree[[r]][[1]]$Targets)+1), nrow = cartdepth)
    colnames(relerrs)  <- c(names(tree[[r]][[1]]$Targets), "MultiTarget")
    cartpdepth    <- length(tree_prune[[r]])
    relerrs_prune <- matrix(ncol = (length(tree_prune[[r]][[1]][!is.na(tree_prune[[r]][[1]]$Targets)]$Targets)+1), nrow = cartpdepth)
    colnames(relerrs_prune) <- c(names(tree_prune[[r]][[1]]$Targets), "MultiTarget")
    for (l in 1:cartdepth) {
      for (z in 1:length(tree[[1]][[1]]$Targets)) {
        nodeprop <- as.numeric(tree[[r]][[l]]$N)/as.numeric(nrow(data))
        if (nodeprop > 0) {
          if (targets$Definitions[z]=="Cont") {
            #relerrs[l,z] <- sqrt(as.numeric(as.character(tree[[r]][[l]]$Targets[[z]]$MSE))) * nodeprop
            relerrs[l,z] <- as.numeric(as.character(tree[[r]][[l]]$Targets[[z]]$MSE)) * nodeprop
          }
          else if (targets$Definitions[z]=="Cat") {
            relerrs[l,z] <- as.numeric(as.character(tree[[r]][[l]]$Targets[[z]]$expectedloss)) * nodeprop
          }
          else {
            relerrs[l,z] <- as.numeric(as.character(tree[[r]][[l]]$Targets[[z]]$deviance)) * nodeprop
          }
        }
        else {next}
      }
      if (!is.null(wt)) {relerrs[l,(length(tree[[r]][[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs[l,]), w=(wt), na.rm=TRUE)}
      else {relerrs[l,(length(tree[[r]][[1]]$Targets)+1)] <- as.numeric(as.character(mean(as.numeric(relerrs[l,]), na.rm=TRUE)))}
    }
    carterrslist[[r]] <- relerrs
    for (c in 1:ncol(relerrs)) {
      cart_evals[r,c] <- mean(relerrs[,c], na.rm = TRUE)
    }
    rm(relerrs)
    for (l in 1:cartpdepth) {
      if (length(tree_prune[[r]][[1]][!is.na(tree_prune[[r]][[1]]$Targets)]$Targets)>0) {
        for (z in 1:length(tree_prune[[1]][[1]]$Targets)) {
          nodeprop <- as.numeric(tree_prune[[r]][[l]]$N)/as.numeric(nrow(data))
          if (targets$Definitions[z]=="Cont") {
            relerrs_prune[l,z] <- as.numeric(as.character(tree_prune[[r]][[l]]$Targets[[z]]$MSE)) * nodeprop
          }
          else if (targets$Definitions[z]=="Cat") {
            relerrs_prune[l,z] <- as.numeric(as.character(tree_prune[[r]][[l]]$Targets[[z]]$expectedloss)) * nodeprop
          }
          else {
            relerrs_prune[l,z] <- as.numeric(as.character(tree_prune[[r]][[l]]$Targets[[z]]$deviance)) * nodeprop
          }
        }
      }
      if (!is.null(wt) && length(tree_prune[[r]][[1]][!is.na(tree_prune[[r]][[1]]$Targets)]$Targets)>0) {relerrs_prune[l,(length(tree_prune[[r]][[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs_prune[l,]), w=(wt), na.rm=TRUE)}
      else if (length(tree_prune[[r]][[1]][!is.na(tree_prune[[r]][[1]]$Targets)]$Targets)>0) {relerrs_prune[l,(length(tree_prune[[r]][[1]]$Targets)+1)] <- as.numeric(as.character(mean(as.numeric(relerrs_prune[l,]), na.rm=TRUE)))}
      else {next}
    }
    cartperrslist[[r]] <- relerrs_prune
    for (c in 1:ncol(relerrs_prune)) {
      cart_evals_prune[r,c] <- mean(relerrs_prune[,c], na.rm = TRUE)
    }
    rm(relerrs_prune)
  }
  cart_evals <- data.frame(cart_evals)
  cart_evals$id <- rownames(cart_evals)
  cartnames <- data.frame(cartnames)
  cartnames$id <- rownames(cartnames)
  carttrainerr <- merge(cartnames, cart_evals, by="id")
  carttrainerr$id <- as.numeric(carttrainerr$id)
  cart_evals_prune <- data.frame(cart_evals_prune)
  cart_evals_prune$id <- rownames(cart_evals_prune)
  cartptrainerr <- merge(cartnames, cart_evals_prune, by="id")
  cartptrainerr$id <- as.numeric(cartptrainerr$id)
  #Extract & Tabulate Testing Error for Unpruned & Pruned Trees
  # **** Update for case where test tree has empty nodes -> no target data
  if (!is.null(testdata)) {
    cart_test           <- matrix(ncol = (length(treetest[[1]][[1]]$Targets)+1), nrow = (depth+1))
    colnames(cart_test) <- c(names(treetest[[1]][[1]]$Targets), "MultiTarget")
    carttestlist        <- vector(mode = "list", length = length(depth+1))
    cart_test_prune           <- matrix(ncol = (length(treetest_prune[[1]][[1]]$Targets)+1), nrow = (depth+1))
    colnames(cart_test_prune) <- c(names(treetest_prune[[1]][[1]]$Targets), "MultiTarget")
    cartptestlist             <- vector(mode = "list", length = length(depth+1))
    for (r in 1:(depth+1)) {
      cartdepth <- length(treetest[[r]])
      relerrs   <- matrix(ncol = (length(treetest[[1]][[1]]$Targets)+1), nrow = cartdepth)
      colnames(relerrs)  <- c(names(treetest[[1]][[1]]$Targets), "MultiTarget")
      cartpdepth    <- length(treetest_prune[[r]])
      relerrs_prune <- matrix(ncol = (length(treetest_prune[[1]][[1]]$Targets)+1), nrow = cartpdepth)
      colnames(relerrs_prune) <- c(names(treetest_prune[[1]][[1]]$Targets), "MultiTarget")
      if (nrow(relerrs_prune)>0) {
        for (l in 1:cartdepth) {
          for (z in 1:length(treetest[[1]][[1]]$Targets)) {
            nodeprop <- as.numeric(treetest[[r]][[l]]$N)/as.numeric(nrow(testdata))
            if (targets$Definitions[z]=="Cont" & any(!is.na(treetest[[r]][[l]]$Targets))) {
              #relerrs[l,z] <- sqrt(as.numeric(as.character(treetest[[r]][[l]]$Targets[[z]]$MSE))) * nodeprop
              relerrs[l,z] <- as.numeric(as.character(treetest[[r]][[l]]$Targets[[z]]$MSE)) * nodeprop
            }
            else if (targets$Definitions[z]=="Cat" & any(!is.na(treetest[[r]][[l]]$Targets))) {
              relerrs[l,z] <- as.numeric(as.character(treetest[[r]][[l]]$Targets[[z]]$expectedloss)) * nodeprop
            }
            else if (any(!is.na(treetest[[r]][[l]]$Targets))) {
              relerrs[l,z] <- as.numeric(as.character(treetest[[r]][[l]]$Targets[[z]]$deviance)) * nodeprop
            }
          }
          if (!is.null(wt)) {relerrs[l,(length(treetest[[r]][[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs[l,]), w=(wt), na.rm=TRUE)}
          else {relerrs[l,(length(treetest[[r]][[1]]$Targets)+1)] <- as.numeric(as.character(mean(as.numeric(relerrs[l,]), na.rm=TRUE)))}
        }
        carttestlist[[r]] <- relerrs
        relerrs[is.nan(relerrs)]<-NA
        for (c in 1:ncol(relerrs)) {
          cart_test[r,c] <- mean(relerrs[,c], na.rm = TRUE)
        }
        rm(relerrs)
        for (l in 1:cartpdepth) {
          for (z in 1:length(treetest_prune[[1]][[1]]$Targets)) {
            nodeprop <- as.numeric(treetest_prune[[r]][[l]]$N)/as.numeric(nrow(testdata))
            if (targets$Definitions[z]=="Cont" & any(!is.na(treetest[[r]][[l]]$Targets))) {
              #relerrs_prune[l,z] <- sqrt(as.numeric(as.character(treetest_prune[[r]][[l]]$Targets[[z]]$MSE))) * nodeprop
              relerrs_prune[l,z] <- as.numeric(as.character(treetest_prune[[r]][[l]]$Targets[[z]]$MSE)) * nodeprop
            }
            else if (targets$Definitions[z]=="Cat" & any(!is.na(treetest[[r]][[l]]$Targets))) {
              relerrs_prune[l,z] <- as.numeric(as.character(treetest_prune[[r]][[l]]$Targets[[z]]$expectedloss)) * nodeprop
            }
            else if (any(!is.na(treetest[[r]][[l]]$Targets))) {
              relerrs_prune[l,z] <- as.numeric(as.character(treetest_prune[[r]][[l]]$Targets[[z]]$deviance)) * nodeprop
            }
          }
          if (!is.null(wt)) {relerrs_prune[l,(length(treetest_prune[[r]][[1]]$Targets)+1)] <- weighted.mean(as.numeric(relerrs_prune[l,]), w=(wt), na.rm=TRUE)}
          else {relerrs_prune[l,(length(treetest_prune[[r]][[1]]$Targets)+1)] <- as.numeric(as.character(mean(as.numeric(relerrs_prune[l,]), na.rm=TRUE)))}
        }
        cartptestlist[[r]] <- relerrs_prune
        relerrs_prune[is.nan(relerrs_prune)]<-NA
        for (c in 1:ncol(relerrs_prune)) {
          cart_test_prune[r,c] <- mean(relerrs_prune[,c], na.rm = TRUE)
        }
      }
      rm(relerrs_prune)
    }
    cart_test <- data.frame(cart_test)
    cart_test$id <- rownames(cart_test)
    carttesterr <- merge(cartnames, cart_test, by="id")
    carttesterr$id <- as.numeric(carttesterr$id)
    cart_test_prune <- data.frame(cart_test_prune)
    cart_test_prune$id <- rownames(cart_test_prune)
    cartptesterr <- merge(cartnames, cart_test_prune, by="id")
    cartptesterr$id <- as.numeric(cartptesterr$id)
    #Return results
    returnlist <- list((carttrainerr), (cartptrainerr), (carttesterr), (cartptesterr), (cols))
  }
  else {
    #Return results
    returnlist <- list((carttrainerr), (cartptrainerr), (cols))
  }
  return(returnlist)
}

#############################################################
#                   Simulation Experiments                  #
#############################################################

# Data generation/permutation for simulation experiments

simulate <- function(simn, nrange, crange, erange, yrange, trange, drange, xrange, method){
  simdat <- matrix(ncol = (15), nrow = 0)
  colnames(simdat) <- c("Sim","SampleSize","TargetType","NumberTargets","NumberFeatures","Correlation","Error","Method","Depth","IGcutoff","Time","TrainError","TestError","TDR","FDR")
  for (s in simn) {
    message("------------------")
    message(paste("Simulation ", paste(s, ":", sep = ""), sep = ""))
    for (n in nrange) {
      n <- ceiling(10^(n))
      message(paste("  Sample Size = ", n, sep = ""))
      for (c in crange) {
        message(paste("  Inter-Target Correlation = ", c, sep = ""))
        for (e in erange) {
          message(paste("  Feature-Target Noise = ", e, sep = ""))
          for (x in xrange) {
            Xn <- x #ceiling(10^(x))
            message(paste("  No. Features = ", Xn, sep = ""))
            for (y in yrange) {
              #Continous target
              if(y==1){
                message("  Target Type = Continuous")
                #set.seed(1234)
                #Simulate t targets
                for(t in trange){
                  message(paste("  No. Targets = ", t, sep = ""))
                  message("  ...Generating Synthetic Data")
                  #Initialize identity matrix for target data generation
                  sigma0 <- diag(t)
                  #Generate positive definite covariance matrix values with correlation c
                  sigmalist <- (sample(1:10, t, replace=TRUE) )
                  for (i in 1:nrow(sigma0)) {
                    for (v in 1:ncol(sigma0)) {
                      if(i==v){sigma0[i,v] <- sigmalist[v]}
                      else {next}
                    }
                  }
                  for (i in 1:nrow(sigma0)) {
                    for (v in 1:ncol(sigma0)) {
                      if(v<i){sigma0[i,v] <- (abs(c))*(sqrt(sigma0[i,i]*sigma0[v,v]))}
                      else {next}
                    }
                  }
                  for (i in 1:nrow(sigma0)) {
                    for (v in 1:ncol(sigma0)) {
                      if(v>i){sigma0[i,v] <- sigma0[v,i]}
                      else {next}
                    }
                  }
                  #Create the mean vector
                  mu <- (sample(1:100, t, replace=TRUE) )
                  #Generate multivariate normally distributed targets
                  df_Z     <- as.data.frame(mvrnorm(n=n, mu=mu, Sigma=sigma0))
                  df_Ztype <- list("Definitions"=rep("Cont",t),"Z"=df_Z)
                  #Define ground truth in features (10 features): 3 binary, 2 categorical (k=3), 5 continuous
                  #df_total <- df_Z
                  nams <- c()
                  for (i in 1:Xn) {
                    nams[i] <- paste("X",i,sep="")
                  }
                  df_X        <- as.data.frame(matrix(ncol=0, nrow=nrow(df_Z)))
                  df_X[,c(nams)] <- NA
                  #Generate all Xn features randomly
                  genfeatures <- c(1:Xn)
                  for (i in genfeatures) {
                    #Generate random binary/categorical features
                    if (i <= Xn/2) {
                      #Binary feature (Bernoulli distribution)
                      if (i <= Xn*0.3) {
                        set.seed(s*n*(c+1)*y*i)
                        df_X[,which(colnames(df_X)==nams[i])] <- rbinom(nrow(df_X),size=1,prob=0.5)
                      }
                      #Categorical feature
                      else {
                        set.seed(s*n*(c+1)*y*i)
                        df_X[,which(colnames(df_X)==nams[i])] <- sample(c("G1","G2","G3"),nrow(df_X), replace = TRUE, p=c(1.0/3, 1.0/3, 1.0/3))
                      }
                    }
                    else {next}
                  }
                  #Generate random continuous features
                  set.seed(s*n*(c+1)*y*i)
                  #Initialize identity matrix for continuous feature data generation
                  sigma0 <- diag(floor(Xn/2))
                  #Generate positive definite covariance matrix values with correlation c
                  sigmalist <- (sample(1:10, floor(Xn/2), replace=TRUE) )
                  for (i in 1:nrow(sigma0)) {
                    for (v in 1:ncol(sigma0)) {
                      if(i==v){sigma0[i,v] <- sigmalist[v]}
                      else {next}
                    }
                  }
                  for (i in 1:nrow(sigma0)) {
                    for (v in 1:ncol(sigma0)) {
                      if(v<i){sigma0[i,v] <- (abs(c_x))*(sqrt(sigma0[i,i]*sigma0[v,v]))}
                      else {next}
                    }
                  }
                  for (i in 1:nrow(sigma0)) {
                    for (v in 1:ncol(sigma0)) {
                      if(v>i){sigma0[i,v] <- sigma0[v,i]}
                      else {next}
                    }
                  }
                  #Create the mean vector
                  mu <- (sample(1:100, floor(Xn/2), replace=TRUE) )
                  #Generate multivariate normally distributed targets
                  df_X_temp     <- as.data.frame(mvrnorm(n=n, mu=mu, Sigma=sigma0))
                  df_X[,((ceiling(Xn/2)+1):Xn)] <- df_X_temp #rnorm(nrow(df_X), mean = 1, sd = 1)

                  for (i in 1:(Xn/2)) {
                    df_X[,which(colnames(df_X)==nams[i])] <- as.factor(as.character(df_X[,which(colnames(df_X)==nams[i])]))
                  }
                  df_total_temp <- df_X

                  message("  ...Defining Ground Truth")
                  #set.seed(1234)
                  #Randomly determine number of partitions (splits) to include in ground truth tree
                  numgtparts <- (sample(2:5, 1, replace=TRUE) )
                  #Randomly select features for ground truth tree generation
                  gtfeatures <- (sample(1:Xn, numgtparts, replace=TRUE) )
                  #Define all nodes for ground truth tree
                  leaf_ids <- vector(mode = "list", length = (2^(numgtparts)+1))
                  leaf_ids[[1]] <- df_X
                  for (i in 1:numgtparts) {
                    df_X_temp <- leaf_ids[[i]]
                    #print(paste("node: ", i, sep = ""))
                    #Subset data using ground truth rule for binary/categorical features
                    if (gtfeatures[i] <= Xn/2) {
                      #Follows rule, to left
                      leaf_ids[[2*i]] <- df_X_temp[which(df_X_temp[,gtfeatures[i]] == names(which.max(table(df_X_temp[,gtfeatures[i]])))), c(1:ncol(df_X_temp))]
                      #print(paste(gtfeatures[i], paste(" = ", names(which.max(table(df_X_temp[,gtfeatures[i]]))), sep = ""), sep=""))
                      #or to the right
                      leaf_ids[[2*i+1]] <- df_X_temp[which(df_X_temp[,gtfeatures[i]] != names(which.max(table(df_X_temp[,gtfeatures[i]])))), c(1:ncol(df_X_temp))]
                    }
                    #Subset data using ground truth rule for continuous features
                    else {
                      quantGTfeat  <- (sample(3:7, 1, replace=TRUE) )
                      featquant <- quantile(df_X_temp[,gtfeatures[i]], probs = seq(0,1,(1/quantGTfeat)))
                      featquant <- featquant[2:(length(featquant)-1)]
                      featquantval <- (sample(1:length(featquant), 1, replace=TRUE) )
                      #Follows rule, to left
                      leaf_ids[[2*i]] <- df_X_temp[which(df_X_temp[,gtfeatures[i]] >= as.numeric(featquant[[featquantval]])), c(1:ncol(df_X_temp))]
                      print(paste(gtfeatures[i], paste(" >= ", as.numeric(featquant[[featquantval]]), sep = ""), sep=""))
                      #or to the right
                      leaf_ids[[2*i+1]] <- df_X_temp[which(df_X_temp[,gtfeatures[i]] < as.numeric(featquant[[featquantval]])), c(1:ncol(df_X_temp))]
                    }
                  }
                  #Extract terminal nodes and link with observation ids
                  df_total_temp$node <- NA
                  leaf_ids[sapply(leaf_ids, is.null)] <- NULL
                  for (i in 1:length(leaf_ids)) {
                    # if the node is not terminal, continue to next
                    if ((2*i+1) <= length(leaf_ids)) {
                      i <- i+1
                    }
                    # if the node is terminal, find observation ids and add node number to df_total_temp
                    else {
                      noderows <- row.names(leaf_ids[[i]])
                      for (nn in noderows) {
                        df_total_temp[nn,]$node <- i
                      }
                    }
                  }
                  #Assign outcomes to data by terminal node
                  targetquantlist <- c()
                  for (i in 1:t) {
                    targetquantlist[i] <- paste("V",i,sep="")
                  }
                  df_total_temp[,c(targetquantlist)] <- NA
                  for (i in 1:t) {
                    #print(paste("Target: ", i, sep = ""))
                    #Divide target i into node many quantiles
                    targquant <- quantile(df_Z[,i], probs = seq(0,1,(1/length(levels(as.factor(df_total_temp$node))))))
                    #print(targquant)
                    #targquant <- targquant[2:length(targquant)]
                    tquantord <- (sample(1:length(levels(as.factor(df_total_temp$node))), length(levels(as.factor(df_total_temp$node))), replace=FALSE) )
                    for (nn in 1:length(levels(as.factor(df_total_temp$node)))) {
                      nlab <- levels(as.factor(df_total_temp$node))[nn]
                      #print(paste("Node: ", nlab, sep = ""))
                      #Subset target values by quantile for leaf node n
                      targvallist <- df_Z[which(df_Z[i] <= targquant[[(tquantord[nn])+1]] & df_Z[i] > targquant[[tquantord[nn]]]), i]
                      #print(paste(colnames(df_Z[i]), paste(" > ", targquant[[tquantord[nn]]], sep = ""), sep = ""))
                      #Sample without replacement for all observations of leaf node n
                      df_total_temp[which(as.factor(df_total_temp$node) == nlab), (Xn+1+i)] <- (sample(targvallist, length(df_total_temp[which(as.factor(df_total_temp$node) == nlab), (Xn+1+i)]), replace=TRUE) )
                      #print(summary(df_total_temp[which(as.factor(df_total_temp$node) == nlab), (Xn+1+i)]))
                    }
                  }
                  df_total <- df_total_temp[,c((Xn+2):(Xn+1+t),1:Xn)]
                  GTcols <- (gtfeatures)
                  #Data partition (60/40) on total data set #set.seed(1234)
                  message("  ...Partitioning Synthetic Data")

                  trainobs <- sort(sample(nrow(df_total), nrow(df_total)*.6))
                  df_train <- df_total[ trainobs,]
                  df_test  <- df_total[-trainobs,]
                  #Run models
                  rm(printdat)
                  printdat <- matrix(ncol = (15), nrow = 0)
                  colnames(printdat) <- c("Sim","SampleSize","TargetType","NumberTargets","NumberFeatures","Correlation","Error","Method","Depth","IGcutoff","Time","TrainError","TestError","TDR","FDR")
                  for (m in 1:length(method)) {
                    #Run CART (single-target) models
                    if (method[m]=="CART") {
                      rm(start_time,end_time,rntime)
                      start_time <- Sys.time()
                      #print("  ...Running Single-Target CART Models")
                      #Run cart models (carttrainerr), (cartptrainerr), (carttesterr), (cartptesterr), (colnums per depth)
                      Zlist  <- colnames(df_Z)
                      targets    <- df_Ztype_Train   <- df_Ztype
                      df_Ztype_Train[[2]] <- df_train[,c(1:ncol(df_Z))]
                      #Create object to store model runs for different targets & depths
                      CART_Z <- matrix(ncol = (7), nrow = 0)
                      colnames(CART_Z) <- c("Z","Zname","Depth","TrainError","TestError","TDR","FDR")
                      colZ   <- c(1:t)
                      #Run single-target models and compute multi-target errors & TDR/FDR for each target
                      for (z in 1:length(Zlist)) {
                        message(paste("  ...Running Single-Target CART Models: Target ", z, sep=""))
                        outcome  <- Zlist[[z]] #Name of target of interest
                        #colZtemp <- colZ[-z]   #List of targets not used in model iteration
                        #Pruned Train & Test MT Error
                        variables <- colnames(df_train[,-c(1:ncol(df_Z))])
                        #CARTsim  <- CART_MTEval(depth=(max(drange)-1), data=df_train[,-c(colZtemp)], testdata=df_test[,-c(colZtemp)], outcome, Zlist[[z]] ~ ., method="anova", cp=0.02)
                        cart_eq <- as.formula(paste(outcome, paste(variables, collapse = " + "), sep = " ~ "))
                        #CARTsim  <- CART_MTEval(depth=(max(drange)-1), data=df_train, testdata=df_test, targets=df_Ztype_Train, outcome, Equation=cart_eq, method="anova", cp=0.02)
                        CARTsim  <- (CART_MTEval(depth=(max(drange)-1), data=df_train, testdata=df_test, targets=df_Ztype_Train, outcome, Equation=cart_eq, method="anova", cp=0.02))
                        #Calculate TDR & FDR
                        TDR <- FDR <- vector(mode = "list", length = length(drange))
                        for (d in drange) {
                          TDR[[d]] <- (sum(as.numeric(unlist(CARTsim[[5]][[d]])-length(df_Ztype_Train$Definitions))   %in% GTcols))  / (length(GTcols))
                          FDR[[d]] <- (sum(!(as.numeric(unlist(CARTsim[[5]][[d]])-length(df_Ztype_Train$Definitions)) %in% GTcols))) / (length(CARTsim[[5]][[d]]))
                          if(is.na(TDR[[d]])) {
                            TDR[[d]] <- 0 #FDR[[d]] <- 0
                          }
                          else {next}
                        }
                        for (d in drange) {
                          CART_Z <- rbind(CART_Z, c(z,Zlist[[z]],d,CARTsim[[2]]$MultiTarget[[d]],CARTsim[[4]]$MultiTarget[[d]],TDR[[d]],FDR[[d]]))
                        }
                        #root_eval <- MTSummary(targets=df_Ztype, data=df_train)
                      }
                      #Aggregate multi-target info from single target models by model depth
                      CART_Z <- as.data.frame(CART_Z)
                      CART_Z$TrainError <- as.numeric(as.character(CART_Z$TrainError))
                      CART_Z$TestError  <- as.numeric(as.character(CART_Z$TestError))
                      CART_Z$TDR        <- as.numeric(as.character(CART_Z$TDR))
                      CART_Z$FDR        <- as.numeric(as.character(CART_Z$FDR))
                      CART              <- aggregate(CART_Z[, c(4:7)], list(CART_Z$Depth), mean)
                      do.call(cbind, lapply(CART, is.nan))
                      CART$TDR[is.nan(CART$TDR)] <- 0
                      CART$FDR[is.nan(CART$FDR)] <- 0
                      end_time <- Sys.time()
                      rntime <- difftime(end_time, start_time, units = "secs")
                      #Add to simulation matrix results
                      for (d in drange) {
                        CARTtemp <- CART[which(CART$Group.1==d),c(1:ncol(CART))]
                        TrEr <- CARTtemp$TrainError
                        TeEr <- CARTtemp$TestError
                        tdr  <- CARTtemp$TDR
                        fdr  <- CARTtemp$FDR
                        simdat <- rbind(simdat, c(s,n,y,t,(Xn),c,e,m,d,NA,rntime[[1]],TrEr,TeEr,tdr,fdr))
                        printdat <- rbind(printdat, c(s,n,y,t,(Xn),c,e,m,d,NA,rntime[[1]],TrEr,TeEr,tdr,fdr))
                      }
                    }
                    #Run MTpart (multi-target) models
                    else {
                      #print("  ...Running Multi-Target Models")
                      message(paste("  ...Running Multi-Target Models: ", method[m], sep=""))
                      #Generate objects to store values for each depth
                      TrainError <- TestError <- TDR <- FDR <- vector(mode = "list", length = length(drange))
                      targets    <- df_Ztype_Train   <- df_Ztype
                      df_Ztype_Train[[2]] <- df_train[,c(1:ncol(df_Z))]
                      df_X_Train          <- df_train[,c((ncol(df_Z)+1):ncol(df_train))]
                      for (d in drange) {
                        #Run multi-target models with error-based splitting
                        if (method[m]=="splitError") {
                          rm(start_time,end_time,rntime)
                          start_time <- Sys.time()
                          parallelsplit <- NA
                          ifelse(Xn >= 100, parallelsplit <- 10, parallelsplit <- "all")
                          #run mtpart with error option
                          rulerun <- suppressMessages(suppressWarnings(MTPart(df_X_Train, df_Ztype_Train, data=df_train, continuous = "quantile", IGcutoff=0, alpha=0.05, cp=0.02,
                                                                              reuse = TRUE, parallelpart = TRUE, parallelsplit=parallelsplit, paralleldepth = 1, depth = d)))
                          end_time <- Sys.time()
                          rntime <- difftime(end_time, start_time, units = "secs")
                          #rulerun <- suppressMessages(suppressWarnings(MTPart(df_X, df_Ztype, data=df_total, continuous = "quantile", IGcutoff=0, alpha=0.05, cp=0.02, reuse = TRUE, parallelpart = TRUE, parallelsplit=parallelsplit, paralleldepth = 1, depth = d)))
                          MTcols <- c()
                          for (i in 1:length(rulerun[[2]])) {
                            #Get partitioning nodes & data colnumbers
                            if (!is.null(rulerun[[2]][[i]]) && !is.na(rulerun[[2]][[i]]$CP)) {
                              #partvarnum <- which(colnames(df_train)==rulerun[[2]][[i]]$Var)
                              partvarnum <- which(colnames(df_X_Train)==rulerun[[2]][[i]]$PartVar)
                              MTcols <- c(MTcols, partvarnum)
                            }
                            #else {i <- i+1}
                          }
                          #MTcols <- unique(MTcols)
                          #Calculate TDR & FDR
                          TDR[[d]] <- (sum(MTcols %in% GTcols))    / (length(GTcols))
                          FDR[[d]] <- (sum(!(MTcols %in% GTcols))) / (length(MTcols))

                          do.call(cbind, lapply(TDR[[d]], is.nan))
                          TDR[[d]][is.nan(TDR[[d]])] <- 0
                          do.call(cbind, lapply(FDR[[d]], is.nan))
                          FDR[[d]][is.nan(FDR[[d]])] <- 0

                          #Prune tree & calculate training error
                          rulerun_p <- MTPrune(tree=rulerun, targets, cp=0.02)
                          evaltab   <- as.data.frame(rulerun_p[[3]])
                          TrainError[[d]] <- evaltab[c(nrow(evaltab)),]$error
                          #Apply pruned tree to test set

                          df_Ztype_Test      <- df_Ztype
                          df_Ztype_Test[[2]] <- df_test[,c(1:ncol(df_Z))]
                          df_X_Test          <- df_test[,c((ncol(df_Z)+1):ncol(df_test))]

                          rulerun_ptest <- MTTest(rulerun_p, df_X_Test, df_Ztype_Test, df_test)
                          #Calculate test error
                          rulerun_ptestSum <- MTPrune(tree=rulerun_ptest, targets, cp=0) #
                          evalTesttab      <- as.data.frame(rulerun_ptestSum[[3]])
                          TestError[[d]]   <- evaltab[c(nrow(evalTesttab)),]$error
                          #Add to simulation matrix results
                          simdat <- rbind(simdat, c(s,n,y,t,(Xn),c,e,m,d,NA,rntime[[1]],TrainError[[d]],TestError[[d]],TDR[[d]],FDR[[d]]))
                          printdat <- rbind(printdat, c(s,n,y,t,(Xn),c,e,m,d,NA,rntime[[1]],TrainError[[d]],TestError[[d]],TDR[[d]],FDR[[d]]))
                          }
                        #Run multi-target models with 6 IG-based splitting options
                        else if (method[m]=="mostIG") {
                          for (ig in IGcutoff) {
                            rm(start_time,end_time,rntime)
                            start_time <- Sys.time()
                            rulerun <- suppressMessages(suppressWarnings(MTPart(df_X_Train, df_Ztype_Train, data=df_train, continuous = "quantile", IGcutoff=ig, alpha=0.05, cp=0.02,
                                                                                evalmethod = method[m], reuse = TRUE, parallelpart = FALSE, depth = d)))
                            end_time <- Sys.time()
                            rntime <- difftime(end_time, start_time, units = "secs")

                            MTcols <- c()
                            for (i in 1:length(rulerun[[2]])) {
                              #Get partitioning nodes & data colnumbers
                              if (!is.null(rulerun[[2]][[i]]) && !is.na(rulerun[[2]][[i]]$CP)) {
                                #partvarnum <- which(colnames(df_train)==rulerun[[2]][[i]]$Var)
                                partvarnum <- which(colnames(df_X_Train)==rulerun[[2]][[i]]$PartVar)
                                MTcols <- c(MTcols, partvarnum)
                              }
                            }
                            #Calculate TDR & FDR
                            TDR[[d]] <- (sum(MTcols %in% GTcols))    / (length(GTcols))
                            FDR[[d]] <- (sum(!(MTcols %in% GTcols))) / (length(MTcols))

                            do.call(cbind, lapply(TDR[[d]], is.nan))
                            TDR[[d]][is.nan(TDR[[d]])] <- 0
                            do.call(cbind, lapply(FDR[[d]], is.nan))
                            FDR[[d]][is.nan(FDR[[d]])] <- 0

                            #Prune tree & calculate training error
                            rulerun_p <- MTPrune(tree=rulerun, targets, cp=0.02)
                            evaltab   <- as.data.frame(rulerun_p[[3]])
                            TrainError[[d]] <- evaltab[c(nrow(evaltab)),]$error
                            #Apply pruned tree to test set

                            df_Ztype_Test      <- df_Ztype
                            df_Ztype_Test[[2]] <- df_test[,c(1:ncol(df_Z))]
                            df_X_Test          <- df_test[,c((ncol(df_Z)+1):ncol(df_test))]

                            rulerun_ptest <- MTTest(rulerun_p, df_X_Test, df_Ztype_Test, df_test)
                            #Calculate test error
                            rulerun_ptestSum <- MTPrune(tree=rulerun_ptest, targets, cp=0) #
                            evalTesttab      <- as.data.frame(rulerun_ptestSum[[3]])
                            TestError[[d]]   <- evaltab[c(nrow(evalTesttab)),]$error

                            #Add to simulation matrix results
                            simdat <- rbind(simdat, c(s,n,y,t,(Xn),c,e,m,d,ig,rntime[[1]],TrainError[[d]],TestError[[d]],TDR[[d]],FDR[[d]]))
                            printdat <- rbind(printdat, c(s,n,y,t,(Xn),c,e,m,d,ig,rntime[[1]],TrainError[[d]],TestError[[d]],TDR[[d]],FDR[[d]]))
                          }
                        }
                        else {
                          rm(start_time,end_time,rntime)
                          start_time <- Sys.time()
                          #run mtpart with specified method
                          rulerun <- suppressWarnings(suppressMessages(MTPart(df_X_Train, df_Ztype_Train, data=df_train, continuous = "quantile", IGcutoff=IGcutoff, alpha=0.05, cp=0.02,
                                            evalmethod = method[m], reuse = TRUE, parallelpart = FALSE, depth = d)))
                          end_time <- Sys.time()
                          rntime <- difftime(end_time, start_time, units = "secs")
                          MTcols <- c()
                          for (i in 1:length(rulerun[[2]])) {
                            #Get partitioning nodes & data colnumbers
                            if (!is.null(rulerun[[2]][[i]]) && !is.na(rulerun[[2]][[i]]$CP)) {
                              #partvarnum <- which(colnames(df_train)==rulerun[[2]][[i]]$Var)
                              partvarnum <- which(colnames(df_X_Train)==rulerun[[2]][[i]]$PartVar)
                              MTcols <- c(MTcols, partvarnum)
                            }
                            #else {i <- i+1}
                          }
                          #MTcols <- unique(MTcols)
                          #Calculate TDR & FDR
                          TDR[[d]] <- (sum(MTcols %in% GTcols))    / (length(GTcols))
                          FDR[[d]] <- (sum(!(MTcols %in% GTcols))) / (length(MTcols))

                          do.call(cbind, lapply(TDR[[d]], is.nan))
                          TDR[[d]][is.nan(TDR[[d]])] <- 0
                          do.call(cbind, lapply(FDR[[d]], is.nan))
                          FDR[[d]][is.nan(FDR[[d]])] <- 0

                          #Prune tree & calculate training error
                          rulerun_p <- MTPrune(tree=rulerun, targets, cp=0.02)
                          evaltab   <- as.data.frame(rulerun_p[[3]])
                          TrainError[[d]] <- evaltab[c(nrow(evaltab)),]$error
                          #Apply pruned tree to test set

                          df_Ztype_Test      <- df_Ztype
                          df_Ztype_Test[[2]] <- df_test[,c(1:ncol(df_Z))]
                          df_X_Test          <- df_test[,c((ncol(df_Z)+1):ncol(df_test))]

                          rulerun_ptest <- MTTest(rulerun_p, df_X_Test, df_Ztype_Test, df_test)
                          #Calculate test error
                          rulerun_ptestSum <- MTPrune(tree=rulerun_ptest, targets, cp=0) #
                          evalTesttab      <- as.data.frame(rulerun_ptestSum[[3]])
                          TestError[[d]]   <- evaltab[c(nrow(evalTesttab)),]$error
                          #Add to simulation matrix results
                          simdat <- rbind(simdat, c(s,n,y,t,(Xn),c,e,m,d,NA,rntime[[1]],TrainError[[d]],TestError[[d]],TDR[[d]],FDR[[d]]))
                          printdat <- rbind(printdat, c(s,n,y,t,(Xn),c,e,m,d,NA,rntime[[1]],TrainError[[d]],TestError[[d]],TDR[[d]],FDR[[d]]))
                        }
                        }
                    }
                  }
                  message("  Model Evaluations:")
                  print(printdat)
                }
              }
              #Categorical target
              if(y==2){}
              #Event rate target
              if(y==3){}
              #Time to event target
              if(y==4){}
            }
          }
        }
      }
    }
  }
  return(simdat)
}

####################### Experiment Setup ####################

#For each experiment, 500 random trees are generated as different ground truths, and training and test set pairs are created using each tree.
#The quality measures are calculated over all 500 instances of the problem, and in the figures we present the means of each measure with the
#standard error indicated by the error ribbon around each line.

#In these experiments we compare our MTPart method to the standard CART heuristic.

#Each experiment varies one parameter while holding all others constant. Unless otherwise specified, the experiments are run with 𝑛 = 1000
#training points in 𝑝 =10 features and T = 4 targets, the ground truth trees are depth 𝐷 = 4, there is no correlation between targets, and no
#noise added to the training data.

simn   <- 1:100
nrange <- 2
crange <- 0
erange <- 0
yrange <- 1
trange <- 4
drange <- 4
xrange <- 10
c_x <- 0
IGcutoff <- 0.95
method <- c("CART","avgIG","maxIG","mostIG","avgPVal","minPVal","mostPVal","splitError")

######################## 1. Sample Size #####################

# The effect of the number of observations
set.seed(1234)
nrange <- seq(2, 3, by=(1/3))

Contsim_n100_1000 <- simulate(simn, nrange, crange, erange, yrange, trange, drange, xrange, method)

######################## 2. Correlation #####################

# The effect of inter-target correlation
set.seed(1234)
crange <- seq(0, 1, by=.25)

Contsim_c0_1 <- simulate(simn, nrange, crange, erange, yrange, trange, drange, xrange, method)

######################## 3. No. Targets #####################

# The effect of noise in feature-target ground truth relationships (c_x - inter-target correlation)
set.seed(1234)
erange <- seq(0, 1, by=.2)

Contsim_e0_1 <- simulate(simn, nrange, crange, erange, yrange, trange, drange, xrange, method)

########################## 4. Depth #########################

#The effect of the number of model complexity
set.seed(1234)
drange <- 1:6

Contsim_d1_6 <- simulate(simn, nrange, crange, erange, yrange, trange, drange, xrange, method)

####################### 5. No. Features #####################

#The effect of the number of the number of features
set.seed(1234)
xrange <- (seq(20, 100, by=(20)))

Contsim_x1_3 <- simulate(simn, nrange, crange, erange, yrange, trange, drange, xrange, method)

#############################################################
#             Motivational Example: LGG Dataset             #
#############################################################

#################### Import & Format Data ###################

df <- read.csv("LGG_example.csv")

set.seed(1234)
trainobs <- createDataPartition(df$death01, p = .6, list = FALSE, times = 1)
x_train <- df[ trainobs,]
x_test  <- df[-trainobs,]

############### Define inputs for functions #################

# Features of Interest
FeatureNames <- c("X1p_19q_co_del_status","IDH1","ARID1A",
                  "ARID1B","ATRX","BCOR","BRAF","CHD2","CHD4",
                  "CHD5","CHD7","CHD8","CHEK2","CIC","CREBBP",
                  "DNMT3A","DOT1L","EGFR","EHMT2","EIF1AX",
                  "EZH1","FUBP1","H3F3A","H3F3C","HDAC2",
                  "HDAC4","HDAC6","KAT6B","KDM4C","KDM5B","MAX",
                  "MLLT3","NCOR1","NCOR2","NF1","NIPBL","NOTCH1",
                  "PDGFRA","PIK3CA","PIK3R1","PLCG1","PRDM2",
                  "PTEN","PTPN11","RB1","RET","SATB1","SETD2",
                  "SMARCA4","SMARCB1","SMARCC1","SMARCC2","TCF12",
                  "TET2","TP53","ZBTB20","ZCCHC12")

# Targets of Interest
target_defs <- c("Cat","Cat","Cat","Cat","Surv","Surv","Surv")

TargetNames <- c("Death","ProgFreeSurvEvent","person_neoplasm_cancer_st",
                 "new_tumor","exp_tt_daystolastordeath_death01",
                 "exp_tt_daystonewtumor_newtumor01",
                 "exp_tt_ProgFreeSurvTimedays_ProgFreeSurvEvent01")

SurvData <- c("daystolastordeath","death01","daystonewtumor","newtumor01",
              "ProgFreeSurvTimedays","ProgFreeSurvEvent01")

summary(x_train[, c(TargetNames)])
summary(x_train[, c(FeatureNames)])
summary(x_train[, c(SurvData)])

# Development dataset
data <- x_train[complete.cases(x_train[,c(TargetNames)]), c(TargetNames,SurvData,FeatureNames)]
rownames(data) <- NULL

# Ground Truth (Expert Tree)
gtsplits <- c('X1p_19q_co_del_status','IDH1')

# Incorporate k-fold cross-validation
kfolds <- 10

# Validation dataset
data_test <- x_test[complete.cases(x_test[,c(TargetNames)]), c(TargetNames,SurvData,FeatureNames)]

###################### Tree Evaluation ######################

df_Ztype <- list("Definitions"=target_defs, "Z"=data[,c(TargetNames)])
df_Z     <- data[,c(TargetNames)]
X        <- data[,c(FeatureNames)]
Xn       <- ncol(X[,c(FeatureNames)])
node     <- 15
parallelsplit <- NA
ifelse(Xn >= 100, parallelsplit <- 10, parallelsplit <- "all")

AvgIG_rulerun <- MTPart(X, df_Ztype, data=data, continuous = "all", 
                        IGcutoff=IGcutoff, alpha=0.05, cp=-1.0,
                        evalmethod = "avgIG", reuse = TRUE, 
                        parallelpart = FALSE, depth = 4, nodesize = node, 
                        splitmin = floor(node/splitmin_div))

#############################################################
#             Motivational Example: GA Dataset              #
#############################################################

#################### Import & Format Data ###################

df <- read.csv("GA_example.csv")

set.seed(1234)
trainobs <- createDataPartition(df$death01, p = .6, list = FALSE, times = 1)
x_train <- df[ trainobs,]
x_test  <- df[-trainobs,]

############### Define inputs for functions #################

# Features of Interest
FeatureNames <- c("EBV.positive","MSI.status","Copy.Number.Cluster",
                  "Total.Mutation.Rate","Hypermutated",
                  "MLH1.Epigenetically.Silenced",
                  "CDKN2A.Epigenetically.Silenced","TP53.mutation",
                  "PIK3CA.mutation","KRAS.mutation","ARID1A.mutation",
                  "RHOA.mutation","ARHGAP26.ARHGAP6.CLDN18.Rearrangement",
                  "ABSOLUTE.Ploidy","ABSOLUTE.Purity",
                  "Estimated.Leukocyte.Percentage","Percent.Tumor.Nuclei",
                  "Percent.Tumor.Cells","Percent.Lymphocyte.Infiltration")

# Targets of Interest
target_defs <- c("Cat","Cat","Cat","Cat","Cat","Surv","Surv","Surv")

TargetNames <- c("Death","Recurrence","newtumor","treatment",
                 "neoplasm","exp_tt_daystolastordeath_death01",
                 "exp_tt_daystolastorrec_rec01",
                 "exp_tt_daystolastornewtumor_newtumor01")

SurvData <- c("daystolastordeath","death01","daystolastornewtumor",
              "newtumor01","daystolastorrec","rec01")

summary(x_train[, c(TargetNames)])
summary(x_train[, c(FeatureNames)])
summary(x_train[, c(SurvData)])

# Development dataset
data <- x_train[complete.cases(x_train[,c(TargetNames)]), c(TargetNames,SurvData,FeatureNames)]
rownames(data) <- NULL

# Ground Truth (Expert Tree)
gtsplits <- c("EBV.positive","MSI.status","Copy.Number.Cluster")

# Incorporate k-fold cross-validation
kfolds <- 10

# Validation dataset
data_test <- x_test[complete.cases(x_test[,c(TargetNames)]), c(TargetNames,SurvData,FeatureNames)]

###################### Tree Evaluation ######################

df_Ztype <- list("Definitions"=target_defs, "Z"=data[,c(TargetNames)])
df_Z     <- data[,c(TargetNames)]
X        <- data[,c(FeatureNames)]
Xn       <- ncol(X[,c(FeatureNames)])
node     <- 15
parallelsplit <- NA
ifelse(Xn >= 100, parallelsplit <- 10, parallelsplit <- "all")

SErr_rulerun <- MTPart(X, df_Ztype, data=data, continuous = "quantile", alpha=0.05, cp=-1.0, reuse = TRUE,
                       parallelpart = TRUE, parallelsplit=parallelsplit, paralleldepth = 1,
                       depth = 4, nodesize = node, splitmin = floor(node/splitmin_div))

#############################################################
#             Motivational Example: EC Dataset              #
#############################################################
#################### Import & Format Data ###################

df <- read.csv("EC_example.csv")

set.seed(1234)
trainobs <- createDataPartition(df$death01, p = .6, list = FALSE, times = 1)
x_train <- df[ trainobs,]
x_test  <- df[-trainobs,]

############### Define inputs for functions #################

# Features of Interest
FeatureNames <- c("POLE","PIK3CA","ARID1A","FGFR2","CTNNB1","CHD4",
                  "data_gistic","data_rna_seq","data_core_sample","mhl1_hypermethylated",
                  "msi_status_7_marker_call","cna_cluster_k4")

# Targets of Interest
target_defs <- c("Cat","Cat","Cat","Cat","Surv","Surv","Surv")

TargetNames <- c("death","prog","rec","disease_status_at_lfu",
                 "exp_tt_daystolastordeath_death01",
                 "exp_tt_daystolastornewtumor_prog01")

SurvData <- c("daystolastordeath","death01","daystolastornewtumor",
              "prog01","daystolastorrec","rec01")

summary(x_train[, c(TargetNames)])
summary(x_train[, c(FeatureNames)])
summary(x_train[, c(SurvData)])

# Development dataset
data <- x_train[complete.cases(x_train[,c(TargetNames)]), c(TargetNames,SurvData,FeatureNames)]
rownames(data) <- NULL

# Ground Truth (Expert Tree)
gtsplits <- c("POLE","msi_status_7_marker_call","cna_cluster_k4")

# Incorporate k-fold cross-validation
kfolds <- 10

# Validation dataset
data_test <- x_test[complete.cases(x_test[,c(TargetNames)]), c(TargetNames,SurvData,FeatureNames)]

###################### Tree Evaluation ######################

df_Ztype <- list("Definitions"=target_defs, "Z"=data[,c(TargetNames)])
df_Z     <- data[,c(TargetNames)]
X        <- data[,c(FeatureNames)]
Xn       <- ncol(X[,c(FeatureNames)])
node     <- 15
parallelsplit <- NA
ifelse(Xn >= 100, parallelsplit <- 10, parallelsplit <- "all")

MostP_rulerun <- MTPart(X, df_Ztype, data=data, continuous = "quantile", IGcutoff=IGcutoff, alpha=0.05, cp=-1.0,
                        evalmethod = "mostPVal", reuse = FALSE, parallelpart = FALSE, depth = 4, nodesize = node, splitmin = floor(node/splitmin_div))
SErr_rulerun <- MTPart(X, df_Ztype, data=data, continuous = "quantile", alpha=0.05, cp=-1.0, reuse = TRUE,
                       parallelpart = TRUE, parallelsplit=parallelsplit, paralleldepth = 1,
                       depth = 4, nodesize = node, splitmin = floor(node/splitmin_div))

library(GGally)

ggpairs(x_train[c('POLE','MUC16','KRAS','BCOR')])

explanatory <- c(
  # Demographics
  #"age","BMI","ethnicity","race",
  # Clinical History, Family History, Procedure Characteristics, Diagnostics
  # Histology & Tumor Characteristics
  # "X2009stagegroup","histology","tumor_grade",
  # Symptoms, Therapy, Molecular
  "NFASC","TP53","ABCA13","ARHGAP35","DNAH3","DSCAM","ZFHX4","ARID5B","ASPM","FAT3","NAV2","PIK3R1","PTEN","RYR1","RYR3","TAF1","TENM4",
  "TTN","ZFHX3","CTCF","DNAH9","DSP","DST","GIGYF2","HERC2","KMT2D","KRAS","LAMA2","LRP1","MDN1","MUC16","MUC5B","PIK3CA","RYR2","SPTA1",
  "TENM1","UBR4","APC","ARID1A","ATM","BCOR",
  "BIRC6","CACNA1E","CHD3","DMD","DNAH5","DNHD1","FAT1","HMCN1","LRP1B","MKI67","MUC17","NEB",
  "PXDN","RPL22","SACS","SZT2","USP9X","DNAH10","DNAH7","DYNC1H1","FAT4","FGFR2","FLG","GPR112","LRP2","OBSCN","PCDH15","CTNNB1","KMT2B",
  "USH2A","VPS13B","AHNAK2","EP400","MED12","ANK3","APOB","CNTNAP5","CSMD1","CSMD3","DCHS1","DNAH1","DNAH11","DNAH2","FBXW7","GLI3","GPR98",
  "HECTD4","ITPR1","KMT2C","MACF1","MYH7","PCLO",#"POLE",
  "RNF213","SYNE1","TG","XIRP2","TRRAP","HERC1","CHD4","PLXNA4","NBEA","AKAP9","FLNA",
  "FN1","MUC4","COL11A1","CSMD2","HUWE1","MYCBP2",
  "data_gistic","data_rna_seq","data_core_sample","mhl1_hypermethylated",#"msi_status_5_marker_call",
  "msi_status_7_marker_call","cna_cluster_k4"
  #"Gene.Expression.Cluster","MicroRNA.Expression.Cluster","Methylation.Cluster","CIMP.Category"
)
explanatory <- c("KRAS","MUC16","BCOR","mhl1_hypermethylated",#"msi_status_5_marker_call",
  "msi_status_7_marker_call","cna_cluster_k4"
  #"Gene.Expression.Cluster","MicroRNA.Expression.Cluster","Methylation.Cluster","CIMP.Category"
)

x_train %>%
  mutate(
    POLE = ff_label(POLE, "POLE")
  ) %>%
  summary_factorlist('POLE', explanatory, fit_id=TRUE, digits = c(1, 1, 3, 1), p=TRUE) -> features_table

x_train$cna_cluster_k4 <- as.factor(x_train$cna_cluster_k4)
x_train %>%
  mutate(
    POLE = ff_label(POLE, "POLE")
  ) %>%
  finalfit('POLE', explanatory, fit_id=TRUE) -> features_table


splitError_rulerun <- MTPart(X, df_Ztype, data=data, continuous = "quantile", IGcutoff=IGcutoff, alpha=0.05, cp=-1.0,
                        evalmethod = "splitError", reuse = FALSE, parallelpart = FALSE, depth = 4, nodesize = node, splitmin = floor(node/splitmin_div))


x_train$MostP <- ifelse(x_train$mhl1_hypermethylated==1 & x_train$cna_cluster_k4<3 & x_train$BCOR=="SNV", "Leaf node 1",
                       ifelse(x_train$mhl1_hypermethylated==1 & x_train$cna_cluster_k4<3 & x_train$BCOR=="wt", "Leaf node 2",
                              ifelse(x_train$mhl1_hypermethylated==1 & x_train$cna_cluster_k4>=3, "Leaf node 3",
                                     ifelse(x_train$mhl1_hypermethylated==0 & x_train$cna_cluster_k4<2 & x_train$KRAS=="SNV", "Leaf node 4",
                                            ifelse(x_train$mhl1_hypermethylated==0 & x_train$cna_cluster_k4<2 & x_train$KRAS=="wt", "Leaf node 5",
                                                   ifelse(x_train$mhl1_hypermethylated==0 & x_train$cna_cluster_k4>=2 & x_train$MUC16=="SNV", "Leaf node 6",
                                                          ifelse(x_train$mhl1_hypermethylated==0 & x_train$cna_cluster_k4>=2 & x_train$MUC16=="wt", "Leaf node 7", NA)))))))
x_train$MostP <- factor(x_train$MostP, levels = c("Leaf node 7", "Leaf node 1", "Leaf node 2", "Leaf node 3", "Leaf node 4", "Leaf node 5", "Leaf node 6"))

x_train$MostP <- NA
x_train$MostP <- ifelse(x_train$mhl1_hypermethylated==1 & x_train$cna_cluster_k4 < 2, "Leaf node 1",
                        ifelse(x_train$mhl1_hypermethylated==1 & x_train$cna_cluster_k4 >= 2, "Leaf node 2",
                               ifelse(x_train$mhl1_hypermethylated !=1 & x_train$POLE=="SNV", "Leaf node 3",
                                      ifelse(x_train$mhl1_hypermethylated !=1 & x_train$POLE !="SNV" & x_train$cna_cluster_k4 < 2, "Leaf node 4",
                                             ifelse(x_train$mhl1_hypermethylated !=1 & x_train$POLE !="SNV" & x_train$cna_cluster_k4 >= 2, "Leaf node 5", NA)))))
table(x_train$MostP)
table(x_train$mhl1_hypermethylated)
table(x_train$cna_cluster_k4)
table(x_train$POLE)

x_train$MostP <- factor(x_train$MostP, levels = c("Leaf node 5", "Leaf node 1", "Leaf node 2", "Leaf node 3", "Leaf node 4"))

#Create dummy variables for multi-level treatment outcome

x_trainb <- x_train
x_trainb$MostP <- as.factor(ifelse(!is.na(x_train$MostP), "Overall", NA))
x_train2 <- rbind(x_train, x_trainb)
#x_train2$MostP <- factor(x_train2$MostP, levels = c("Overall", "Leaf node 1", "Leaf node 2", "Leaf node 3", "Leaf node 4", "Leaf node 5"))

#Analysis of all leaves (take largest as ref)

explanatory2 = c("death","prog","rec","disease_status_at_lfu","daystolastordeath","daystolastornewtumor","daystolastorrec")
dependent = "MostP"

x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))]  %>%
  mutate(
    MostP = ff_label(MostP, "MTPart (Most P-Value) Subtypes")
  ) %>%
  summary_factorlist(dependent, explanatory2, fit_id=TRUE, digits = c(1, 1, 3, 1))  -> EC_desc

explanatory = "MostP"
dependent1 = "death"
dependent2 = "prog"
dependent3 = "rec"
dependent4 = "disease_status_at_lfu"
dependent5  =  "Surv(daystolastordeath,death01)"
dependent6  =  "Surv(daystolastornewtumor,prog01)"
dependent7  =  "Surv(daystolastorrec,rec01)"

x_train$MostP <- factor(x_train$MostP, levels = c("Leaf node 5","Leaf node 1", "Leaf node 2", "Leaf node 3", "Leaf node 4"))

x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))]  %>%
  mutate(
    MostP = ff_label(MostP, "MTPart (SplitError) Subtypes")
  ) %>%
  summary_factorlist(NULL, explanatory, fit_id=TRUE, digits = c(1, 1, 3, 1))  %>%
  ff_merge(
    glmuni(x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))] , dependent1, explanatory) %>%
      fit2df(estimate_suffix=" (Death)")
  ) %>%
  ff_merge(
    glmuni(x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))] , dependent2, explanatory) %>%
      fit2df(estimate_suffix=" (Progression)")
  ) %>%
  ff_merge(
    glmuni(x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))] , dependent3, explanatory) %>%
      fit2df(estimate_suffix=" (Recurrence)")
  ) %>%
  ff_merge(
    glmuni(x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))] , dependent4, explanatory) %>%
      fit2df(estimate_suffix=" (Treatment Response: Stable & Progressive Disease)")
  ) %>%
  ff_merge(
    coxphuni(x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))] , dependent5, explanatory) %>%
      fit2df(estimate_suffix=" (OS)")
  ) %>%
  ff_merge(
    coxphuni(x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))] , dependent6, explanatory) %>%
      fit2df(estimate_suffix=" (PFS)")
  ) %>%
  ff_merge(
    coxphuni(x_train[which(!is.na(x_train$MostP)), c(1:ncol(x_train))] , dependent7, explanatory) %>%
      fit2df(estimate_suffix=" (RFS)")
  ) -> t
#############################################################
