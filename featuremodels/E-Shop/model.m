eShop : Store_front Business_management :: _eShop ;

Store_front : [Home_page] [Registration] Catalog [Wish_list] Buy_paths [Customer_service] [User_behaviour_tracking] :: _Store_front ;

Home_page : sg_Home_page6+ :: _Home_page ;

sg_Home_page6 : Static_content_7
	| Content_type9 Variation_source13 :: Dynamic_content8 ;

Content_type9 : sg_Content_type910+ :: _Content_type9 ;

sg_Content_type910 : Welcome_message11
	| Special_offers ;

Variation_source13 : sg_Variation_source1314+ :: _Variation_source13 ;

sg_Variation_source1314 : Time_dependent15
	| Personalized16 ;

Registration : Registration_enforcement Registration_information23 [User_behaviour_tracking_information] :: _Registration ;

Registration_enforcement : sg_Registration_enforcement19+ :: _Registration_enforcement ;

sg_Registration_enforcement19 : Register_to_browse20
	| Register_to_buy
	| None22 ;

Registration_information23 : Login_credentials24 [Shipping_address] [Billing_address27] [Credit_card_information29] [Demographics34] [Personal_Information40] [Preferences] [Reminders46] [Quick_checkout_profile] [Custom_fields48] :: _Registration_information23 ;

Shipping_address : [Multiple_shipping_addresses26] :: _Shipping_address ;

Billing_address27 : [Multiple_billing_addresses28] :: _Billing_address27 ;

Credit_card_information29 : Card_holder_name30 Card_number31 Expiry_date32 [Security_information33] :: _Credit_card_information29 ;

Demographics34 : sg_Demographics3435+ :: _Demographics34 ;

sg_Demographics3435 : Age36
	| Income37
	| Education38
	| Custom_Demographic_field39 ;

Preferences : sg_Preferences42+ :: _Preferences ;

sg_Preferences42 : Site_layout43
	| List_size44
	| Language45 ;

Catalog : Product_Information [Categories] [Multiple_catalogs87] [Searching88] [Browsing92] [Custom_views103] :: _Catalog ;

Product_Information : Product_type Basic_information [Detailed_information] [Warranty_information] [Customer_reviews] [Associated_assets] [Product_variants] [Size] [Weight] [Availability] [Custom_fields] :: _Product_Information ;

Product_type : sg_Product_type53+ :: _Product_type ;

sg_Product_type53 : Eletronic_goods
	| Physical_goods
	| Services ;

Associated_assets : sg_Associated_assets62+ :: _Associated_assets ;

sg_Associated_assets62 : Documents63
	| Media_files64 ;

Media_files64 : sg_Media_files6465+ :: _Media_files64 ;

sg_Media_files6465 : Image66
	| Video74
	| Sound75 ;

Image66 : sg_Image6667+ :: _Image66 ;

sg_Image6667 : Thumbnail68
	| a2D_image69
	| a3D_image70
	| a360_degrees_image71
	| Different_perspectives72
	| Gallery73 ;

Product_variants : [Complex_product_configuration77] :: _Product_variants ;

Categories : categories_catalog :: _Categories ;

categories_catalog : [Categories84] :: _categories_catalog ;

Categories84 : [Multi_level85] [Multiple_classification86] :: _Categories84 ;

Searching88 : sg_Searching8889+ :: _Searching88 ;

sg_Searching8889 : Basic_search90
	| Advanced_search91 ;

Browsing92 : Product_page93 [Category_page] [Index_page95] :: _Browsing92 ;

Index_page95 : [Sorting_filters96] :: _Index_page95 ;

Sorting_filters96 : sg_Sorting_filters9697+ :: _Sorting_filters96 ;

sg_Sorting_filters9697 : Price98
	| Quality99
	| Price_Quality_ratio_100
	| Manufacturer_name101
	| Custom_filter102 ;

Custom_views103 : [Seasonal_product_views104] [Personalized_views105] :: _Custom_views103 ;

Wish_list : [Wish_list_save_after_session] [E_mail_wish_list] [Multiple_wish_lists109] [Permissions] :: _Wish_list ;

Permissions : sg_Permissions111+ :: _Permissions ;

sg_Permissions111 : Public_access112
	| Restricted_access113
	| Private_access114 ;

Buy_paths : Shopping_cart116 Checkout121 Order_confirmation181 :: _Buy_paths ;

Shopping_cart116 : Inventory_management_policy117 Cart_content_page118 [Cart_summary_page119] [Cart_save_after_session120] :: _Shopping_cart116 ;

Checkout121 : Checkout_type122 [Shipping_options] Taxation_options134 Payment_options159 :: _Checkout121 ;

Checkout_type122 : sg_Checkout_type122123+ :: _Checkout_type122 ;

sg_Checkout_type122123 : Registered_checkout
	| Guest_checkout127 ;

Registered_checkout : [Quick_checkout] :: _Registered_checkout ;

Quick_checkout : [Enable_profile_update_on_checkout_126] :: _Quick_checkout ;

Shipping_options : [Quality_of_service_selection129] [Carrier_selection130] [Gift_options131] [Multiple_shipments132] Shipping_cost_calculation133 :: _Shipping_options ;

Taxation_options134 : sg_Taxation_options134135+ :: _Taxation_options134 ;

sg_Taxation_options134135 : Type137 Ammount_specification150 :: Custom_taxation136
	| Tax_gateways154 ;

Type137 : sg_Type137138+ :: _Type137 ;

sg_Type137138 : Fixed_rate_taxation139
	| Tax_codes141 Address142 [Resolution145] :: Rule_based_taxation140 ;

Address142 : Shipping [Billing144] :: _Address142 ;

Resolution145 : sg_Resolution145146+ :: _Resolution145 ;

sg_Resolution145146 : Country147
	| Region148
	| City149 ;

Ammount_specification150 : sg_Ammount_specification150151+ :: _Ammount_specification150 ;

sg_Ammount_specification150151 : Surcharge152
	| Percentage153 ;

Tax_gateways154 : sg_Tax_gateways154155+ :: _Tax_gateways154 ;

sg_Tax_gateways154155 : CertiTAX156
	| CyberSource157
	| Custom_tax_gateway158 ;

Payment_options159 : Payment_types160 [Fraud_detection171] [Payment_gateways172] :: _Payment_options159 ;

Payment_types160 : sg_Payment_types160161+ :: _Payment_types160 ;

sg_Payment_types160161 : COD162
	| Credit_card163
	| Debit_card164
	| Eletronic_cheque165
	| Fax_mail_order166
	| Purchase_order167
	| Gift_certificate168
	| Phone_order169
	| Custom_payment_type170 ;

Payment_gateways172 : sg_Payment_gateways172173+ :: _Payment_gateways172 ;

sg_Payment_gateways172173 : Authorize_Net174
	| CyberSource175
	| LinkPoint176
	| Paradata177
	| SkipJack178
	| Verisign_Payflow_Pro179
	| Custom_payment_gateway180 ;

Order_confirmation181 : sg_Order_confirmation181182+ :: _Order_confirmation181 ;

sg_Order_confirmation181182 : Eletronic_page183
	| E_mail184
	| Phone185
	| Mail186 ;

Customer_service : sg_Customer_service188+ :: _Customer_service ;

sg_Customer_service188 : Question_and_feedback_forms189
	| Product_returns191
	| Filtering_criteria193 [Request_order_hardcopy198] :: Order_status_review192
	| Shipment_status_tracking_199 ;

Question_and_feedback_forms189 : [Question_and_feedback_tracking190] :: _Question_and_feedback_forms189 ;

Filtering_criteria193 : sg_Filtering_criteria193194+ :: _Filtering_criteria193 ;

sg_Filtering_criteria193194 : Order_number195
	| Order_date196
	| Order_status197 ;

Shipment_status_tracking_199 : sg_Shipment_status_tracking_199200+ :: _Shipment_status_tracking_199 ;

sg_Shipment_status_tracking_199200 : Internal_tracking201
	| Partner_tracking202 ;

User_behaviour_tracking : Behaviour_tracked204 :: _User_behaviour_tracking ;

Behaviour_tracked204 : sg_Behaviour_tracked204205+ :: _Behaviour_tracked204 ;

sg_Behaviour_tracked204205 : Locally_visited_pages
	| External_referring_pages
	| Previous_purchases ;

Business_management : Order_management210 [Targeting239] [Affiliates299] [Inventory_tracking] [Procurement] [Reporting_and_analysis] [External_systems_integration313] Administration319 :: _Business_management ;

Order_management210 : Fulfillment211 :: _Order_management210 ;

Fulfillment211 : sg_Fulfillment211212+ :: _Fulfillment211 ;

sg_Fulfillment211212 : Warehouse_management shipping :: Physical_goods_fulfillment
	| File_repository234 License_management235 :: Eletronic_goods_fulfillment
	| [Appointment_scheduling237] [Resource_planning238] :: Services_fulfillment ;

shipping : sg_shipping216+ :: _shipping ;

sg_shipping216 : Custom_shipping_method217
	| Shipping_gateways226 ;

Custom_shipping_method217 : Pricing218 :: _Custom_shipping_method217 ;

Pricing218 : Flat_rate219 [Rate_factors220] :: _Pricing218 ;

Rate_factors220 : sg_Rate_factors220221+ :: _Rate_factors220 ;

sg_Rate_factors220221 : Quantity_purchased222
	| Order_total223
	| Weight224
	| Product_classification225 ;

Shipping_gateways226 : sg_Shipping_gateways226227+ :: _Shipping_gateways226 ;

sg_Shipping_gateways226227 : FedEX228
	| UPS229
	| USPS230
	| Canada_Post231
	| Custom_shipping_gateway232 ;

Targeting239 : Targeting_criteria240 Targeting_mechanisms251 Display_and_notification291 [Campaigns298] :: _Targeting239 ;

Targeting_criteria240 : sg_Targeting_criteria240241+ :: _Targeting_criteria240 ;

sg_Targeting_criteria240241 : Customer_preferences
	| Personal_information243
	| Demographics244
	| targeting_criteria_previous_purchases
	| Shopping_cart_content246
	| Wish_list_content
	| Previously_visited_pages
	| Date_and_time249
	| Custom_target_criteria250 ;

Targeting_mechanisms251 : sg_Targeting_mechanisms251252+ :: _Targeting_mechanisms251 ;

sg_Targeting_mechanisms251252 : Advertisement_types254 Advertisement_sources258 [Advertisement_response_tracking263] [Context_sensitive_ads264] :: Advertisements253
	| Discount_conditions266 Award270 Eligibility_requirements275 Graduation_by278 [Coupons282] Handling_multiple_discounts283 :: Discounts
	| Sell_strategies284 ;

Advertisement_types254 : sg_Advertisement_types254255+ :: _Advertisement_types254 ;

sg_Advertisement_types254255 : Banner_ads256
	| Pop_up_ads257 ;

Advertisement_sources258 : sg_Advertisement_sources258259+ :: _Advertisement_sources258 ;

sg_Advertisement_sources258259 : House_advertisements260
	| Paid_advertisements261 ;

Paid_advertisements261 : Advertisement_management_interface262 :: _Paid_advertisements261 ;

Discount_conditions266 : Product_and_quantity_scope267 Time_scope268 [Purchase_value_scope269] :: _Discount_conditions266 ;

Award270 : sg_Award270271+ :: _Award270 ;

sg_Award270271 : Percentage_discount272
	| Fixed_discount273
	| Free_item274 ;

Eligibility_requirements275 : [Customer_segments276] [Shipping_address277] :: _Eligibility_requirements275 ;

Graduation_by278 : sg_Graduation_by278279+ :: _Graduation_by278 ;

sg_Graduation_by278279 : Purchase_value280
	| Quantity281 ;

Sell_strategies284 : sg_Sell_strategies284285+ :: _Sell_strategies284 ;

sg_Sell_strategies284285 : Product_kitting286
	| Up_selling287
	| Cross_selling289 ;

Up_selling287 : Substitute_products288 :: _Up_selling287 ;

Cross_selling289 : Past_customers_also_bought290 :: _Cross_selling289 ;

Display_and_notification291 : sg_Display_and_notification291292+ :: _Display_and_notification291 ;

sg_Display_and_notification291292 : Assignment_to_page_types_for_display293
	| Product_flagging294
	| [Personalized] [Response_tracking297] :: E_mails295 ;

Affiliates299 : Affiliate_registration300 Commission_tracking301 :: _Affiliates299 ;

Inventory_tracking : [Allow_backorders303] :: _Inventory_tracking ;

Procurement : Stock_replenishment305 :: _Procurement ;

Stock_replenishment305 : Manual306 [Automatic] :: _Stock_replenishment305 ;

Automatic : Non_repudiation_service308 :: _Automatic ;

Reporting_and_analysis : Report_types310 Report_formats_311 Level_of_detail312 :: _Reporting_and_analysis ;

External_systems_integration313 : sg_External_systems_integration313314+ :: _External_systems_integration313 ;

sg_External_systems_integration313314 : Fulfillment_system
	| Inventory_management_system316
	| Procurement_system
	| External_distributor_system318 ;

Administration319 : Content_management320 Store_administration325 :: _Administration319 ;

Content_management320 : Product_database_management321 Presentation_options322 General_layout_management323 [Content_approval324] :: _Content_management320 ;

Store_administration325 : Site_search326 Search_engine_registration327 Domain_name_setup328 :: _Store_administration325 ;

%%

not Special_offers or Discounts ;
not Registered_checkout or Registration_enforcement ;
not Registered_checkout or Register_to_buy ;
not Customer_preferences or Preferences ;
not Quick_checkout or Quick_checkout_profile ;
not User_behaviour_tracking_information or User_behaviour_tracking ;
not Eletronic_goods or Eletronic_goods_fulfillment ;
not Physical_goods or Physical_goods_fulfillment ;
not Services or Services_fulfillment ;
not Physical_goods or Size ;
not Eletronic_goods or Size ;
not Physical_goods or Weight ;
not Availability or Inventory_tracking ;
not Category_page or Categories ;
not Wish_list or Wish_list_save_after_session ;
Registration or Wish_list_save_after_session ;
not E_mail_wish_list or Registration ;
not Permissions or Registration ;
not Shipping_options or shipping ;
not Wish_list_content or Wish_list ;
not Previously_visited_pages or Locally_visited_pages or External_referring_pages ;

